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

from typing import Any, Dict, Iterator, Iterable, List, Tuple, Union

from collections import namedtuple
import sys

from . import sexp as sx
from .core import UnexpectedError, REPLDriver, \
    Hypothesis, Goal, Message, Sentence, Text, Fragment, \
    PrettyPrinted, PosView, indent, debug
from .coq import CoqIdents

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

class SerAPI(REPLDriver):
    BIN = "sertop"
    NAME = "Coq+SerAPI"
    REPL_ARGS = ("--printer=sertop", "--implicit")

    ID = "sertop"
    LANGUAGE = "coq"

    # Whether to silently continue past unexpected output
    EXPECT_UNEXPECTED: bool = False

    MIN_PP_MARGIN = 20
    DEFAULT_PP_ARGS = {'pp_depth': 30, 'pp_margin': 55}

    # pylint: disable=dangerous-default-value
    def __init__(self, args=(),
                 fpath="-",
                 binpath=None,
                 pp_args: Dict[str, Any]=DEFAULT_PP_ARGS):
        """Prepare to run ``sertop``."""
        super().__init__(args=args, fpath=fpath, binpath=binpath)
        self.instance_args = ("--topfile={}".format(self.topfile),)
        self.next_qid = 0
        self.pp_args: Dict[str, Any] = {**SerAPI.DEFAULT_PP_ARGS, **pp_args}
        self.last_response = None

    @classmethod
    def driver_not_found(cls, binpath):
        MSG = ("`sertop` binary not found (bin={});"
               " please run `opam install coq-serapi`")
        raise ValueError(MSG.format(binpath))

    @property
    def topfile(self):
        return CoqIdents.topfile_of_fpath(self.fpath)

    @property
    def metadata(self):
        return {"sertop_args": self.user_args}

    def _next_sexp(self):
        """Wait for the next sertop prompt, and return the output preceding it."""
        response = self._read()
        if not response: # pragma: no cover
            # https://github.com/ejgallego/coq-serapi/issues/212
            MSG = "SerTop printed an empty line.  Last response: {!r}."
            raise UnexpectedError(MSG.format(self.last_response))
        debug(response, '<< ')
        self.last_response = response
        try:
            return sx.load(response)
        except sx.ParseError: # pragma: no cover
            return response

    def _send(self, sexp):
        s = sx.dump([b'query%d' % self.next_qid, sexp])
        self.next_qid += 1
        self._write(s, b'\n')

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
            raise UnexpectedError("Unexpected answer: {}".format(sexp))

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
            raise UnexpectedError("Unexpected feedback: {}".format(sexp))

    def _deserialize_response(self, sexp):
        tag = sexp_hd(sexp)
        if tag == b'Answer':
            yield from SerAPI._deserialize_answer(sexp[2])
        elif tag == b'Feedback':
            yield from SerAPI._deserialize_feedback(sexp[1])
        elif not self.EXPECT_UNEXPECTED: # pragma: no cover
            UNEXPECTED = "Unexpected response: {}"
            # Print early to get some information out even if sertop hangs
            print(UNEXPECTED.format(self.last_response), file=sys.stderr)
            MSG = "Unexpected response: {}\nFull output: {}"
            raise ValueError(MSG.format(self.last_response, self.repl.stdout.read()))

    @staticmethod
    def highlight_substring(chunk, beg, end):
        prefix, substring, suffix = chunk[:beg], chunk[beg:end], chunk[end:]
        prefix = b"\n".join(bytes(prefix).splitlines()[-3:])
        suffix = b"\n".join(bytes(suffix).splitlines()[:3])
        return b"%b>>>%b<<<%b" % (prefix, substring, suffix)

    @staticmethod
    def _highlight_exn(span, chunk, prefix='    '):
        src = SerAPI.highlight_substring(chunk, *span)
        LOC_FMT = ("The offending chunk is delimited by >>>…<<< below:\n{}")
        return LOC_FMT.format(indent(src.decode('utf-8', 'ignore'), prefix))

    @staticmethod
    def _clip_span(loc, chunk):
        loc = loc or (0, len(chunk))
        return max(0, loc[0]), min(len(chunk), loc[1])

    @staticmethod
    def _range_of_span(span, chunk):
        return chunk.translate_span(*span) if isinstance(chunk, PosView) else None

    def _warn_on_exn(self, response, chunk):
        QUOTE = '  > '
        ERR_FMT = "Coq raised an exception:\n{}"
        msg = sx.tostr(response.exn)
        err = ERR_FMT.format(indent(msg, QUOTE))
        span = SerAPI._clip_span(response.loc, chunk)
        if chunk:
            err += "\n" + SerAPI._highlight_exn(span, chunk, prefix=QUOTE)
        err += "\n" + "Results past this point may be unreliable."
        self.observer.notify(chunk.s, err, SerAPI._range_of_span(span, chunk), level=3)

    def _collect_messages(self, typs: Tuple[type, ...], chunk, sid) -> Iterator[Any]:
        warn_on_exn = ApiExn not in typs
        while True:
            for response in self._deserialize_response(self._next_sexp()):
                if isinstance(response, ApiAck):
                    continue
                if isinstance(response, ApiCompleted):
                    return
                if warn_on_exn and isinstance(response, ApiExn):
                    if sid is None or response.sids is None or sid in response.sids:
                        self._warn_on_exn(response, chunk)
                if (not typs) or isinstance(response, typs): # type: ignore
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
        strings: List[ApiString] = list(self._collect_messages((ApiString,), None, sid))
        if strings:
            assert len(strings) == 1
            return PrettyPrinted(sid, strings[0].string)
        raise UnexpectedError("No string found in Print answer")

    def _pprint_message(self, msg: ApiMessage):
        return self._pprint(msg.msg, msg.sid, b'CoqPp', **self.pp_args)

    def _exec(self, sid, chunk):
        self._send([b'Exec', sid])
        messages: List[ApiMessage] = list(self._collect_messages((ApiMessage,), chunk, sid))
        return [self._pprint_message(msg) for msg in messages]

    def _add(self, chunk):
        self._send([b'Add', [], sx.escape(chunk)])
        prev_end, spans, messages = 0, [], []
        responses: Iterator[Union[ApiAdded, ApiMessage]] = \
            self._collect_messages((ApiAdded, ApiMessage), chunk, None)
        for response in responses:
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
        goals: List[Goal] = list(self._collect_messages((Goal,), chunk, sid))
        yield from (self._pprint_goal(g, sid) for g in goals)

    def _warn_orphaned(self, chunk, message):
        err = "Orphaned message for sid {}:".format(message.sid)
        err += "\n" + indent(message.pp, " >  ")
        err_range = SerAPI._range_of_span((0, len(chunk)), chunk)
        self.observer.notify(chunk.s, err, err_range, level=2)

    def run(self, chunk):
        """Send a `chunk` to sertop.

        A chunk is a string containing Coq sentences or comments.  The sentences
        are split, sent to Coq, and returned as a list of ``Text`` instances
        (for whitespace and comments) and ``Sentence`` instances (for code).
        """
        chunk = PosView(chunk)
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
            if fragment is None: # pragma: no cover
                self._warn_orphaned(chunk, message)
            else:
                fragment.messages.append(Message(message.pp))
        return fragments

    def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
        with self as api:
            return [api.run(chunk) for chunk in chunks]

class SerAPI_noexec(SerAPI):
    """A variant of SerAPI that segments the code without executing it.

    This runs faster, but the results don't include goals and messages."""

    NAME = "Coq+SerAPI-noexec"
    ID = "sertop_noexec"

    def _exec(self, sid, chunk):
        return []
    def _goals(self, sid, chunk):
        return []

def annotate(chunks: Iterable[str], sertop_args=(), fpath="-", binpath=None) \
    -> List[List[Fragment]]:
    r"""Annotate multiple `chunks` of Coq code.

    >>> annotate(["Check 1."])
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    return SerAPI(args=sertop_args, fpath=fpath, binpath=binpath).annotate(chunks)
