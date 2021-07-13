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

from collections import namedtuple
from collections.abc import Iterable
from textwrap import indent
from sys import stderr

from shlex import quote
from shutil import which
from subprocess import Popen, PIPE, check_output
from . import sexp as sx

DEBUG = False
TRACEBACK = False

def debug(text, prefix):
    if isinstance(text, (bytes, bytearray)):
        text = text.decode("utf-8", errors="replace")
    if DEBUG:
        print(indent(text.rstrip(), prefix), flush=True)

class GeneratorInfo(namedtuple("GeneratorInfo", "name version")):
    def fmt(self, include_version_info=True):
        return "{} v{}".format(self.name, self.version) if include_version_info else self.name

Hypothesis = namedtuple("Hypothesis", "names body type")
Goal = namedtuple("Goal", "name conclusion hypotheses")
Message = namedtuple("Message", "contents")
Sentence = namedtuple("Sentence", "contents messages goals")
Text = namedtuple("Text", "contents")

Goals = namedtuple("Goals", "goals")
Messages = namedtuple("Messages", "messages")
RichSentence = namedtuple("RichSentence", "contents outputs annots prefixes suffixes")

PrettyPrinted = namedtuple("PrettyPrinted", "sid pp")

def sexp_hd(sexp):
    if isinstance(sexp, list):
        return sexp[0]
    return sexp

def utf8(x):
    return str(x).encode('utf-8')

ApiAck = namedtuple("ApiAck", "")
ApiCompleted = namedtuple("ApiCompleted", "")
ApiAdded = namedtuple("ApiAdded", "sid loc")
ApiExn = namedtuple("ApiExn", "sids exn loc")
ApiMessage = namedtuple("ApiMessage", "sid level msg")
ApiString = namedtuple("ApiString", "string")

class SerAPI():
    SERTOP_BIN = "sertop"
    DEFAULT_ARGS = ("--printer=sertop", "--implicit")

    # Whether to silently continue past unexpected output
    EXPECT_UNEXPECTED = False

    # FIXME Pass -topfile (some file in the stdlib fail to compile without it)
    # FIXME Pass --debug when invoked with --traceback

    MIN_PP_MARGIN = 20
    DEFAULT_PP_ARGS = {'pp_depth': 30, 'pp_margin': 55}

    @staticmethod
    def version_info(sertop_bin=SERTOP_BIN):
        bs = check_output([sertop_bin, "--version"])
        return GeneratorInfo("Coq+SerAPI", bs.decode('ascii', 'ignore').strip())

    def __init__(self, args=(), # pylint: disable=dangerous-default-value
                 sertop_bin=SERTOP_BIN,
                 pp_args=DEFAULT_PP_ARGS):
        """Configure and start a ``sertop`` instance."""
        self.args, self.sertop_bin = [*args, *SerAPI.DEFAULT_ARGS], sertop_bin
        self.sertop = None
        self.next_qid = 0
        self.pp_args = {**SerAPI.DEFAULT_PP_ARGS, **pp_args}
        self.last_response = None

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
            msg = ("sertop not found (sertop_bin={});" +
                   " please run `opam install coq-serapi`")
            raise ValueError(msg.format(self.sertop_bin))
        self.kill()
        cmd = [path, *self.args]
        debug(" ".join(quote(s) for s in cmd), '# ')
        self.sertop = Popen(cmd, stdin=PIPE, stderr=stderr, stdout=PIPE)

    def next_sexp(self):
        """Wait for the next sertop prompt, and return the output preceding it."""
        response = self.sertop.stdout.readline()
        if not response:
            # https://github.com/ejgallego/coq-serapi/issues/212
            MSG = "SerTop printed an empty line.  Last response: {!r}."
            raise ValueError(MSG.format(self.last_response))
        debug(response, '<< ')
        self.last_response = response
        try:
            return sx.load(response)
        except sx.ParseError:
            return response

    def _send(self, sexp):
        s = sx.dump([b'query%d' % self.next_qid, sexp])
        self.next_qid += 1
        debug(s, '>> ')
        self.sertop.stdin.write(s + b'\n')
        self.sertop.stdin.flush()

    @staticmethod
    def _deserialize_loc(loc):
        locd = dict(loc)
        return int(locd[b'bp']), int(locd[b'ep'])

    @staticmethod
    def _deserialize_hyp(sexp):
        meta, body, htype = sexp
        assert len(body) <= 1
        body = body[0] if body else None
        ids = [sx.tostr(p[1]) for p in meta if p[0] == b'Id']
        yield Hypothesis(ids, body, htype)

    @staticmethod
    def _deserialize_goal(sexp):
        name = dict(sexp[b'info'])[b'name']
        hyps = [h for hs in reversed(sexp[b'hyp'])
                for h in SerAPI._deserialize_hyp(hs)]
        return Goal(dict(name).get(b'Id'), sexp[b'ty'], hyps)

    @staticmethod
    def _deserialize_answer(sexp):
        tag = sexp_hd(sexp)
        if tag == b'Ack':
            yield ApiAck()
        elif tag == b'Completed':
            yield ApiCompleted()
        elif tag == b'Added':
            yield ApiAdded(sexp[1], SerAPI._deserialize_loc(sexp[2]))
        elif tag == b'ObjList':
            for tag, *obj in sexp[1]:
                if tag == b'CoqString':
                    yield ApiString(sx.tostr(obj[0]))
                elif tag == b'CoqExtGoal':
                    gobj = dict(obj[0])
                    for goal in gobj.get(b'goals', []):
                        yield SerAPI._deserialize_goal(dict(goal))
        elif tag == b'CoqExn':
            exndata = dict(sexp[1])
            opt_loc, opt_sids = exndata.get(b'loc'), exndata.get(b'stm_ids')
            loc = SerAPI._deserialize_loc(opt_loc[0]) if opt_loc else None
            sids = opt_sids[0] if opt_sids else None
            yield ApiExn(sids, exndata[b'str'], loc)
        else:
            raise ValueError("Unexpected answer: {}".format(sexp))

    @staticmethod
    def _deserialize_feedback(sexp):
        meta = dict(sexp)
        contents = meta[b'contents']
        tag = sexp_hd(contents)
        if tag == b'Message':
            mdata = dict(contents[1:])
            # LATER: use the 'str' field directly instead of a Pp call
            yield ApiMessage(meta[b'span_id'], mdata[b'level'], mdata[b'pp'])
        elif tag in (b'FileLoaded', b'ProcessingIn',
                     b'Processed', b'AddedAxiom'):
            pass
        else:
            raise ValueError("Unexpected feedback: {}".format(sexp))

    def _deserialize_response(self, sexp):
        tag = sexp_hd(sexp)
        if tag == b'Answer':
            yield from SerAPI._deserialize_answer(sexp[2])
        elif tag == b'Feedback':
            yield from SerAPI._deserialize_feedback(sexp[1])
        elif not self.EXPECT_UNEXPECTED:
            MSG = "Unexpected response: {}".format(self.last_response)
            raise ValueError(MSG)

    @staticmethod
    def highlight_substring(chunk, beg, end):
        prefix, substring, suffix = chunk[:beg], chunk[beg:end], chunk[end:]
        prefix = b"\n".join(bytes(prefix).splitlines()[-3:])
        suffix = b"\n".join(bytes(suffix).splitlines()[:3])
        return b"%b>>>%b<<<%b" % (prefix, substring, suffix)

    @staticmethod
    def _warn_on_exn(response, chunk):
        ERR_FMT = ("!! Coq raised an exception:\n{}\n"
                   "   Results past this point may be unreliable.\n")
        LOC_FMT = ("   The offending chunk is delimited by >>>.<<< below:\n{}\n")
        msg = sx.tostr(response.exn)
        err = ERR_FMT.format(indent(msg, ' ' * 7))
        if chunk:
            loc = response.loc or (0, len(chunk))
            beg, end = max(0, loc[0]), min(len(chunk), loc[1])
            src = SerAPI.highlight_substring(chunk, beg, end)
            err += LOC_FMT.format(indent(src.decode('utf-8', 'ignore'), ' ' * 7))
        stderr.write(err)

    def _collect_messages(self, types, chunk, sid):
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
                    if sid is None or response.sids is None or sid in response.sids:
                        SerAPI._warn_on_exn(response, chunk)
                if (not types) or isinstance(response, types):
                    yield response

    def _pprint(self, sexp, sid, kind, pp_depth, pp_margin):
        if sexp is None:
            return PrettyPrinted(sid, None)
        if kind is not None:
            sexp = [kind, sexp]
        meta = [[b'sid', sid],
                [b'pp',
                 [[b'pp_format', b'PpStr'],
                  [b'pp_depth', utf8(pp_depth)],
                  [b'pp_margin', utf8(pp_margin)]]]]
        self._send([b'Print', meta, sexp])
        strings = list(self._collect_messages(ApiString, None, sid))
        if strings:
            assert len(strings) == 1
            return PrettyPrinted(sid, strings[0].string)
        raise ValueError("No string found in Print answer")

    def _pprint_message(self, msg):
        return self._pprint(msg.msg, msg.sid, b'CoqPp', **self.pp_args)

    def _exec(self, sid, chunk):
        self._send([b'Exec', sid])
        messages = list(self._collect_messages(ApiMessage, chunk, sid))
        return [self._pprint_message(msg) for msg in messages]

    def _add(self, chunk):
        self._send([b'Add', [], sx.escape(chunk)])
        prev_end, spans, messages = 0, [], []
        for response in self._collect_messages((ApiAdded, ApiMessage), chunk, None):
            if isinstance(response, ApiAdded):
                start, end = response.loc
                if start != prev_end:
                    spans.append((None, chunk[prev_end:start]))
                spans.append((response.sid, chunk[start:end]))
                prev_end = end
            elif isinstance(response, ApiMessage):
                messages.append(response)
        if prev_end != len(chunk):
            spans.append((None, chunk[prev_end:]))
        return spans, [self._pprint_message(msg) for msg in messages]

    def _pprint_hyp(self, hyp, sid):
        d = self.pp_args['pp_depth']
        name_w = max(len(n) for n in hyp.names)
        w = max(self.pp_args['pp_margin'] - name_w, SerAPI.MIN_PP_MARGIN)
        body = self._pprint(hyp.body, sid, b'CoqExpr', d, w - 2).pp
        htype = self._pprint(hyp.type, sid, b'CoqExpr', d, w - 3).pp
        return Hypothesis(hyp.names, body, htype)

    def _pprint_goal(self, goal, sid):
        ccl = self._pprint(goal.conclusion, sid, b'CoqExpr', **self.pp_args).pp
        hyps = [self._pprint_hyp(h, sid) for h in goal.hypotheses]
        return Goal(sx.tostr(goal.name) if goal.name else None, ccl, hyps)

    def _goals(self, sid, chunk):
        # LATER Goals instead and CoqGoal and CoqConstr?
        # LATER We'd like to retrieve the formatted version directly
        self._send([b'Query', [[b'sid', sid]], b'EGoals'])
        goals = list(self._collect_messages(Goal, chunk, sid))
        yield from (self._pprint_goal(g, sid) for g in goals)

    def run(self, chunk):
        """Send a `chunk` to sertop.

        A chunk is a string containing Coq sentences or comments.  The sentences
        are split, sent to Coq, and returned as a list of ``Text`` instances
        (for whitespace and comments) and ``Sentence`` instances (for code).
        """
        if isinstance(chunk, str):
            chunk = chunk.encode("utf-8")
        chunk = memoryview(chunk)
        spans, messages = self._add(chunk)
        fragments, fragments_by_id = [], {}
        for span_id, contents in spans:
            contents = str(contents, encoding='utf-8')
            if span_id is None:
                fragments.append(Text(contents))
            else:
                messages.extend(self._exec(span_id, chunk))
                goals = list(self._goals(span_id, chunk))
                fragment = Sentence(contents, messages=[], goals=goals)
                fragments.append(fragment)
                fragments_by_id[span_id] = fragment
        # Messages for span n + δ can arrive during processing of span n or
        # during _add, so we delay message processing until the very end.
        for message in messages:
            fragment = fragments_by_id.get(message.sid)
            if fragment is None:
                pp = ("\n" + message.pp).replace("\n", "\n   > ")
                MSG = "!! Orphaned message for sid {}:{}\n"
                stderr.write(MSG.format(message.sid, pp))
            else:
                fragment.messages.append(Message(message.pp))
        return fragments

def annotate(chunks, sertop_args=()):
    """Annotate multiple `chunks` of Coq code.

    All fragments are executed in the same Coq instance, started with arguments
    `sertop_args`.  The return value is a list with as many elements as in
    `chunks`, but each element is a list of fragments: either ``Text``
    instances (whitespace and comments) and ``Sentence`` instances (code).

    >>> annotate(["Check 1."], ("-Q", "..,logical_name"))
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    with SerAPI(args=sertop_args) as api:
        return [api.run(chunk) for chunk in chunks]
