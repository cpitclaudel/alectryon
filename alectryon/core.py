# Copyright © 2019 Clément Pit-Claudel
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""Annotate segments of Coq code with responses and goals."""

__version__ = "0.1"
__author__ = 'Clément Pit-Claudel'

from collections import namedtuple
from collections.abc import Iterable
from textwrap import indent
import re
from sys import stderr

from shutil import which #from pexpect.utils
from subprocess import Popen, PIPE, STDOUT
from . import sexp as sx

DEBUG = False
GENERATOR = "Alectryon v{}".format(__version__)

def debug(text, prefix):
    if isinstance(text, (bytes, bytearray)):
        text = text.decode("utf-8")
    if DEBUG:
        print(indent(text.rstrip(), prefix), flush=True)

CoqHypothesis = namedtuple("CoqHypothesis", "name body type")
CoqGoal = namedtuple("CoqGoal", "name conclusion hypotheses")
CoqSentence = namedtuple("CoqSentence", "sentence responses goals")
HTMLSentence = namedtuple("HTMLSentence", "sentence responses goals wsp")
CoqText = namedtuple("CoqText", "string")

def sexp_hd(sexp):
    if isinstance(sexp, list):
        return sexp[0]
    return sexp

ApiAck = namedtuple("ApiAck", "")
ApiCompleted = namedtuple("ApiCompleted", "")
ApiAdded = namedtuple("ApiAdded", "sid loc")
ApiExn = namedtuple("ApiExn", "exn loc")
ApiMessage = namedtuple("ApiMessage", "sid level msg")
ApiString = namedtuple("ApiString", "string")

class SerAPI():
    SERTOP_BIN = "sertop"
    DEFAULT_ARGS = ("--printer=sertop", "--implicit")

    def __init__(self, args=DEFAULT_ARGS, sertop_bin=SERTOP_BIN):
        """Configure and start a ``sertop`` instance."""
        self.args, self.sertop_bin = args, sertop_bin
        self.sertop = None
        self.tag = 0

    def __enter__(self):
        self.reset()
        return self

    def __exit__(self, *_exn):
        self.kill()
        return False

    def kill(self):
        if self.sertop:
            self.sertop.kill()

    def reset(self):
        path = which(self.sertop_bin)
        if path is None:
            raise ValueError("sertop ({}) not found".format(self.sertop_bin))
        self.kill()
        self.sertop = Popen([path, *self.args],
                          stdin=PIPE, stderr=STDOUT, stdout=PIPE)

    def next_sexp(self):
        """Wait for the next sertop prompt, and return the output preceeding it."""
        response = self.sertop.stdout.readline()
        sexp = sx.load(response)
        debug(response, '<< ')
        return sexp

    def _send(self, sexp):
        s = sx.dump([b'query%d' % self.tag, sexp])
        self.tag += 1
        debug(s, '>> ')
        self.sertop.stdin.write(s + b'\n')
        self.sertop.stdin.flush()

    @staticmethod
    def _deserialize_loc(locd):
        return int(locd[b'bp']), int(locd[b'ep'])

    @staticmethod
    def _deserialize_hyp(sexp):
        meta, body, htype = sexp
        assert len(body) <= 1
        name = dict(meta)[b'Id']
        body = body[0] if body else None
        return CoqHypothesis(name, body, htype)

    @staticmethod
    def _deserialize_goal(sexp):
        hyps = [SerAPI._deserialize_hyp(h) for h in reversed(sexp[b'hyp'])]
        return CoqGoal(sexp[b'name'], sexp[b'ty'], hyps)

    @staticmethod
    def _deserialize_answer(sexp):
        tag = sexp_hd(sexp)
        if tag == b'Ack':
            yield ApiAck()
        elif tag == b'Completed':
            yield ApiCompleted()
        elif tag == b'Added':
            meta = dict(sexp[2])
            yield ApiAdded(sexp[1], SerAPI._deserialize_loc(meta))
        elif tag == b'ObjList':
            for tag, *obj in sexp[1]:
                if tag == b'CoqString':
                    yield ApiString(sx.tostr(obj[0]))
                elif tag == b'CoqExtGoal':
                    goal = dict(obj[0])
                    for fg in map(dict, goal.get(b'fg_goals', [])):
                        yield SerAPI._deserialize_goal(fg)
        elif tag == b'CoqExn':
            _, opt_loc, _opt_sids, _bt, exn = sexp
            if opt_loc:
                loc = SerAPI._deserialize_loc(dict(opt_loc[0]))
            else:
                loc = None
            yield ApiExn(exn, loc)
        else:
            raise ValueError("Unexpected answer: {}".format(sexp))

    @staticmethod
    def _deserialize_feedback(sexp):
        meta = dict(sexp)
        contents = meta[b'contents']
        tag = sexp_hd(contents)
        if tag == b'Message':
            yield ApiMessage(meta[b'span_id'], contents[1], contents[3])
        elif tag in (b'FileLoaded', b'ProcessingIn',
                    b'Processed', b'AddedAxiom'):
            pass
        else:
            raise ValueError("Unexpected feedback: {}".format(sexp))

    @staticmethod
    def _deserialize_response(sexp):
        tag = sexp_hd(sexp)
        if tag == b'Answer':
            yield from SerAPI._deserialize_answer(sexp[2])
        elif tag == b'Feedback':
            yield from SerAPI._deserialize_feedback(sexp[1])
        else:
            raise ValueError("Unexpected response: {}".format(sexp))

    @staticmethod
    def _warn_on_exn(response, chunk):
        ERR_FMT = ("Coq raised an exception ({})\n"
                   "Results past this point may be unreliable.\n")
        LOC_FMT = "The offending chunk is delimited by >>>.<<< below:\n{}\n"
        err = ERR_FMT.format(response.exn)
        if chunk:
            loc = response.loc or (0, len(chunk))
            beg, end = max(0, loc[0]), min(len(chunk), loc[1])
            src = b"%b>>>%b<<<%b" % (chunk[:beg], chunk[beg:end], chunk[end:])
            locstr = LOC_FMT.format(indent(src.decode('utf-8'), '    '))
        else:
            locstr = ""
        stderr.write(indent(err + locstr, "!! ", predicate=lambda _: True))

    def _collect_responses(self, types, chunk):
        if isinstance(types, Iterable):
            warn_on_exn = ApiExn not in types
        else:
            warn_on_exn = ApiExn != types
        while True:
            for response in self._deserialize_response(self.next_sexp()):
                if isinstance(response, ApiAck):
                    continue
                if isinstance(response, ApiCompleted):
                    return
                if warn_on_exn and isinstance(response, ApiExn):
                    SerAPI._warn_on_exn(response, chunk)
                if (not types) or isinstance(response, types):
                    yield response

    def _pprint(self, sexp, sid, kind=None):
        if sexp is None:
            return None
        if kind is not None:
            sexp = [kind, sexp]
        meta = [[b'pp_format', b'PpStr']]  # FIXME [b'sid', sid]
        self._send([b'Print', meta, sexp])
        strings = list(self._collect_responses(ApiString, None))
        if strings:
            return strings[0].string
        raise ValueError("No string found in Print answer")

    def _exec(self, sid, chunk):
        self._send([b'Exec', sid])
        messages = list(self._collect_responses(ApiMessage, chunk))
        return [self._pprint(msg.msg, msg.sid, b'CoqPp') for msg in messages]

    def _add(self, chunk):
        self._send([b'Add', [], sx.escape(chunk)])
        prev_end = 0
        for response in self._collect_responses(ApiAdded, chunk):
            start, end = response.loc
            if start != prev_end:
                yield None, chunk[prev_end:start]
            yield response.sid, chunk[start:end]
            prev_end = end
        if prev_end != len(chunk):
            yield None, chunk[prev_end:]

    def _pprint_hyp(self, hyp, sid):
        body = self._pprint(hyp.body, sid, b'CoqExpr')
        htype = self._pprint(hyp.type, sid, b'CoqExpr')
        return CoqHypothesis(sx.tostr(hyp.name), body, htype)

    def _pprint_goal(self, goal, sid):
        conclusion = self._pprint(goal.conclusion, sid, b'CoqExpr')
        hyps = [self._pprint_hyp(h, sid) for h in goal.hypotheses]
        return CoqGoal(sx.tostr(goal.name), conclusion, hyps)

    def _goals(self, span_id, chunk):
        # FIXME Goals instead and CoqGoal and CoqConstr?
        self._send([b'Query', [[b'sid', span_id]], b'EGoals'])
        goals = list(self._collect_responses(CoqGoal, chunk))
        yield from (self._pprint_goal(g, span_id) for g in goals)

    def run(self, chunk):
        """Send a `chunk` to sertop.

        A chunk is a string containing one or more sentences.  The sentences are
        split, sent to Coq, and returned as a list of ``CoqText`` instances
        (for whitespace and comments) and ``CoqSentence`` instances (for code).
        """
        if isinstance(chunk, str):
            chunk = chunk.encode("utf-8")
        chunk = memoryview(chunk)
        spans = list(self._add(chunk))
        fragments = []
        for span_id, contents in spans:
            contents = str(contents, encoding='utf-8')
            if span_id is None:
                fragments.append(CoqText(contents))
            else:
                responses = self._exec(span_id, chunk)
                goals = list(self._goals(span_id, chunk))
                fragment = CoqSentence(contents, responses, goals)
                fragments.append(fragment)
        return fragments

def annotate_chunks(api, chunks):
    """Annotate multiple `chunks` using `api` and yield results."""
    for chunk in chunks:
        yield api.run(chunk)

def annotate(chunks):
    """Annotate multiple `chunks` of Coq code.

    All fragments are executed in the same Coq instance.  The return value is a
    list with as many elements as in `chunks`, but each element is a list of
    ``CoqText`` instances (for whitespace and comments) and ``CoqSentence``
    instances (for code).
    """
    with SerAPI() as api:
        return list(annotate_chunks(api, chunks))

LEADING_BLANKS_RE = re.compile(r'^([ \t]*(?:\n|$))?(.*)$', flags=re.DOTALL)

def isolate_leading_blanks(txt):
    return LEADING_BLANKS_RE.match(txt).groups()

def group_whitespace_with_code(fragments):
    # Move all spaces following a code fragment, up to the first newline, into
    # the code fragment itself; this makes sure that (1) we can hide the newline
    # when we display the goals as a block, and (2) that we don't hide the goals
    # when the user hovers on spaces between two tactics.
    grouped = []
    for fr in fragments:
        if (grouped and isinstance(fr, CoqText)):
            assert isinstance(grouped[-1], HTMLSentence)
            wsp, rest = isolate_leading_blanks(fr.string)
            if wsp: grouped[-1].wsp.append(CoqText(wsp))
            if rest: grouped.append(CoqText(rest))
            continue
        if isinstance(fr, CoqSentence):
            fr = HTMLSentence(fr.sentence, fr.responses, fr.goals, wsp=[])
        grouped.append(fr)
    return grouped
