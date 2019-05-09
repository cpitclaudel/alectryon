#!/usr/bin/env python3

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

import argparse
from collections import namedtuple
from collections.abc import Iterable
import json
import os.path
import re
from textwrap import indent
from sys import stderr

from dominate import tags, document
from dominate.util import raw as dom_raw
from pexpect.utils import which
from pexpect.popen_spawn import PopenSpawn
import sexpdata
import pygments
import pygments.lexers
import pygments.formatters

DEBUG = False
GENERATOR = "Alectryon v{}".format(__version__)

def debug(text, prefix):
    if DEBUG:
        print(indent(text, prefix))

CoqHypothesis = namedtuple("CoqHypothesis", "name body type")
CoqGoal = namedtuple("CoqGoal", "name conclusion hypotheses")
CoqSentence = namedtuple("CoqSentence", "sentence responses goals")
HTMLSentence = namedtuple("HTMLSentence", "sentence responses goals wsp")
CoqText = namedtuple("CoqText", "string")

def remove_symbols(sexp):
    if isinstance(sexp, sexpdata.SExpBase):
        return sexp.value()
    if isinstance(sexp, (int, str)):
        return sexp
    assert isinstance(sexp, list)
    return [remove_symbols(s) for s in sexp]

def sexp_loads(s):
    return remove_symbols(sexpdata.loads(s, nil=None, true=None, false=None))

def sexp_dumps(sexp):
    return sexpdata.dumps(sexp)

def sexp_hd(sexp):
    if isinstance(sexp, (int, str)):
        return sexp
    if not sexp:
        return None
    assert isinstance(sexp, list)
    return sexp[0]

class InlineHtmlFormatter(pygments.formatters.HtmlFormatter):  # pylint: disable=no-member
    def wrap(self, source, _outfile):
        return self._wrap_code(source)

    @staticmethod
    def _wrap_code(source):
        yield from source

LEXER = pygments.lexers.CoqLexer(ensurenl=False)  # pylint: disable=no-member
FORMATTER = InlineHtmlFormatter(nobackground=True)
WHITESPACE_RE = re.compile(r"^(\s*)((?:.*\S)?)(\s*)$", re.DOTALL)

def highlight(coqstr):
    # Pygments HTML formatter adds an unconditional newline, so we pass it only
    # the code, and we restore the spaces after highlighting.
    before, code, after = WHITESPACE_RE.match(coqstr).groups()
    highlighted = pygments.highlight(code, LEXER, FORMATTER).strip()
    return tags.span(before, dom_raw(highlighted), after, cls="highlight")

ApiAck = namedtuple("ApiAck", "")
ApiCompleted = namedtuple("ApiCompleted", "")
ApiAdded = namedtuple("ApiAdded", "sid loc")
ApiExn = namedtuple("ApiExn", "exn loc")
ApiMessage = namedtuple("ApiMessage", "sid level msg")
ApiString = namedtuple("ApiString", "string")

class SerAPI():
    SERTOP_BIN = "sertop"
    SERTOP_PROMPT = re.compile("\0")
    DEFAULT_ARGS = ("--printer=sertop", "--print0", "--implicit")

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
            self.sertop.kill(9)

    def reset(self):
        path = which(self.sertop_bin)
        if not path:
            raise ValueError("sertop ({}) not found".format(self.sertop_bin))
        self.kill()
        self.sertop = PopenSpawn([path, *self.args], encoding="utf-8")
        self.sertop.delaybeforesend = 0

    def next_sexp(self):
        """Wait for the next sertop prompt, and return the output preceeding it."""
        self.sertop.expect(SerAPI.SERTOP_PROMPT, timeout=2)
        response = self.sertop.before
        sexp = sexp_loads(response)
        debug(response, '>> ')
        return sexp

    def _send(self, sexp):
        s = sexp_dumps(["query{}".format(self.tag), sexp])
        self.tag += 1
        debug(s, '<< ')
        return self.sertop.sendline(s)

    @staticmethod
    def _deserialize_hyp(sexp):
        meta, body, htype = sexp
        assert len(body) <= 1
        name = str(dict(meta)["Id"])
        body = body[0] if body else None
        return CoqHypothesis(name, body, htype)

    @staticmethod
    def _deserialize_goal(sexp):
        hyps = [SerAPI._deserialize_hyp(h) for h in reversed(sexp["hyp"])]
        return CoqGoal(str(sexp["name"]), sexp["ty"], hyps)

    @staticmethod
    def _deserialize_answer(sexp):
        tag = sexp_hd(sexp)
        if tag == 'Ack':
            yield ApiAck()
        elif tag == 'Completed':
            yield ApiCompleted()
        elif tag == 'Added':
            meta = dict(sexp[2])
            yield ApiAdded(sexp[1], (meta['bp'], meta['ep']))
        elif tag == 'ObjList':
            for tag, *obj in sexp[1]:
                if tag == "CoqString":
                    yield ApiString(str(obj[0]))
                elif tag == "CoqExtGoal":
                    goal = dict(obj[0])
                    for fg in map(dict, goal.get("fg_goals", ())):
                        yield SerAPI._deserialize_goal(fg)
        elif tag == 'CoqExn':
            _, opt_loc, _opt_sids, _bt, exn = sexp
            if opt_loc:
                d = dict(opt_loc[0])
                loc = d['bp'], d['ep']
            else:
                loc = None
            yield ApiExn(exn, loc)
        else:
            raise ValueError("Unexpected answer: {}".format(sexp))

    @staticmethod
    def _deserialize_feedback(sexp):
        meta = dict(sexp)
        contents = meta['contents']
        tag = sexp_hd(contents)
        if tag == 'Message':
            yield ApiMessage(meta['span_id'], contents[1], contents[3])
        elif tag in ('FileLoaded', 'ProcessingIn', 'Processed'):
            pass
        else:
            raise ValueError("Unexpected feedback: {}".format(sexp))

    @staticmethod
    def _deserialize_response(sexp):
        tag = sexp_hd(sexp)
        if tag == 'Answer':
            yield from SerAPI._deserialize_answer(sexp[2])
        elif tag == 'Feedback':
            yield from SerAPI._deserialize_feedback(sexp[1])
        else:
            raise ValueError("Unexpected response: {}".format(sexp))

    @staticmethod
    def _warn_on_exn(response, chunk):
        ERR_FMT = ("Coq raised an exception ({})\n"
                   "Results past this point may be unreliable.\n"
                   "The offending chunk is delimited by >>>.<<< below:\n{}\n")
        loc = response.loc or (0, len(chunk))
        beg, end = max(0, loc[0]), min(len(chunk), loc[1])
        src = chunk[:beg] + ">>>" + chunk[beg:end] + "<<<" + chunk[end:]
        err = ERR_FMT.format(response.exn, indent(src, '    '))
        stderr.write(indent(err, "!! "))

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
        meta = [['pp_format', 'PpStr']]  # FIXME ['sid', sid]
        self._send(['Print', meta, sexp])
        strings = list(self._collect_responses(ApiString, None))
        if strings:
            return strings[0].string
        raise ValueError("No string found in Print answer")

    def _exec(self, sid, chunk):
        self._send(['Exec', sid])
        messages = list(self._collect_responses(ApiMessage, chunk))
        return [self._pprint(msg.msg, msg.sid, 'CoqPp') for msg in messages]

    def _add(self, chunk):
        self._send(['Add', (), chunk])
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
        body = self._pprint(hyp.body, sid, 'CoqExpr')
        htype = self._pprint(hyp.type, sid, 'CoqExpr')
        return CoqHypothesis(hyp.name, body, htype)

    def _pprint_goal(self, goal, sid):
        conclusion = self._pprint(goal.conclusion, sid, 'CoqExpr')
        hyps = [self._pprint_hyp(h, sid) for h in goal.hypotheses]
        return CoqGoal(goal.name, conclusion, hyps)

    def _goals(self, span_id, chunk):
        # FIXME Goals instead and CoqGoal and CoqConstr?
        self._send(['Query', [['sid', span_id]], 'EGoals'])
        goals = list(self._collect_responses(CoqGoal, chunk))
        yield from (self._pprint_goal(g, span_id) for g in goals)

    def run(self, chunk):
        """Send a `chunk` to sertop.

        A chunk is a string containing one or more sentences.  The sentences are
        split, sent to Coq, and returned as a list of ``CoqText`` instances
        (for whitespace and comments) and ``CoqSentence`` instances (for code).
        """
        spans = list(self._add(chunk))
        fragments = []
        for span_id, contents in spans:
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

def gen_goal_html(goal):
    """Serialize a goal to HTML."""
    with tags.span(cls="coq-goal"):
        if goal.name:
            tags.span(goal.name, cls="goal-name")
        with tags.span(cls="goal-hyps"):
            for hyp in goal.hypotheses:
                with tags.span(cls="goal-hyp"):
                    tags.span(hyp.name, cls="hyp-name")
                    with tags.span():
                        if hyp.body:
                            with tags.span(cls="hyp-body"):
                                tags.span(":=", cls="hyp-punct")
                                highlight(hyp.body)
                        with tags.span(cls="hyp-type"):
                            tags.span(":", cls="hyp-punct")
                            highlight(hyp.type)
        tags.span(cls="goal-separator")
        tags.span(highlight(goal.conclusion), cls="goal-conclusion")

class Gensym():
    def __init__(self):
        self.counter = -1

    def next(self, prefix):
        self.counter += 1
        return hex(self.counter).replace("0x", prefix)

GENSYM = Gensym()

def gen_sentence_html(fr):
    with tags.span(cls="coq-fragment"):
        if fr.goals or fr.responses:
            nm = GENSYM.next("chk")
            tags.input(type="checkbox", id=nm, cls="coq-toggle")
            args = {'for': nm}
        else:
            args = {}
        tags.label(highlight(fr.sentence), cls="coq-sentence", **args)
        with tags.span(cls="coq-output"):
            with tags.span(cls="coq-goals"):
                for goal in fr.goals:
                    gen_goal_html(goal)
            with tags.span(cls="coq-responses"):
                for response in fr.responses:
                    tags.span(highlight(response), cls="coq-response")
        for wsp in getattr(fr, 'wsp', ()):
            tags.span(wsp.string, cls="coq-wsp")

LEADING_BLANKS_RE = re.compile(r'^([ \t]*(?:\n|$))?(.*)$', flags=re.DOTALL)

def isolate_leading_blanks(txt):
    return LEADING_BLANKS_RE.match(txt).groups()

def gen_fragments_html(fragments):
    """Serialize a list of `fragments` to HTML."""
    with tags.pre(cls="alectryon-io") as div:
        tags.comment(" Generator: {} ".format(GENERATOR))
        for fr in fragments:
            if isinstance(fr, CoqText):
                tags.span(highlight(fr.string), cls="coq-nc")
            else:
                assert isinstance(fr, (CoqSentence, HTMLSentence))
                gen_sentence_html(fr)
        return div

ARGDOC = ".\n".join([
    __doc__, "When run as a standalone application, take input as multiple "
    ".v or .json files, and create one .io.json file per input file."
])

COQ_SPLIT_RE = re.compile(r"(\n(?:[ \t]*\n)+)")

def read_input(fpath):
    _fdir, fname = os.path.split(fpath)
    _fn, fext = os.path.splitext(fname)
    if fext == '.v':
        with open(fpath) as src:
            return fname, COQ_SPLIT_RE.split(src.read())
    elif fext == '.json':
        with open(fpath) as src:
            return fname, json.load(src)
    else:
        msg = "Input files must have extension .v or .json ({})."
        raise argparse.ArgumentTypeError(msg.format(fname))

def parse_arguments():
    parser = argparse.ArgumentParser(description=ARGDOC)
    add = parser.add_argument

    INPUT_HELP = """Input file.  Can be either .v (plain Coq code) or \
.json (a list of Coq fragments)."""
    add("input", nargs="+", type=read_input, help=INPUT_HELP)

    WRITER_HELP = """Output type"""
    WRITER_CHOICES = ("json", "html", "webpage")
    add("--writer",
        default="webpage",
        choices=WRITER_CHOICES,
        help=WRITER_HELP)

    DEBUG_HELP = "Print communications with SerAPI."
    add("--debug", action="store_true", default=False, help=DEBUG_HELP)

    return parser.parse_args()

COQ_TYPES = (CoqSentence, CoqGoal, CoqHypothesis, CoqText)
COQ_TYPE_NAMES = {
    "CoqHypothesis": "hypothesis",
    "CoqGoal": "goal",
    "CoqSentence": "sentence",
    "HTMLSentence": "html_sentence",
    "CoqText": "text",
}

def prepare_json(obj):
    if isinstance(obj, list):
        return [prepare_json(x) for x in obj]
    if isinstance(obj, dict):
        return {k: prepare_json(v) for k, v in obj.items()}
    if isinstance(obj, COQ_TYPES):
        d = {k: prepare_json(v) for k, v in zip(obj._fields, obj)}
        nm = COQ_TYPE_NAMES[type(obj).__name__]
        return {"_type": nm, **d}
    return obj

def write_json(fname, annotated):
    with open("{}.io.json".format(fname), mode="w") as out:
        json.dump(prepare_json(annotated), out, indent=4)

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

def gen_html(annotated):
    for idx, fragments in enumerate(annotated):
        if idx > 0:
            yield tags.comment(" alectryon-block-end ")
        yield gen_fragments_html(group_whitespace_with_code(fragments))

def write_html(fname, annotated):
    ts = list(gen_html(annotated))
    with open("{}.snippets.html".format(fname), mode="w") as out:
        for t in ts:
            out.write(t.render(pretty=False))
            out.write('\n')

def write_webpage(fname, annotated):
    doc = document(title=fname)
    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))
    doc.head.add(tags.link(rel="stylesheet", href="alectryon.css"))

    FIRA_CODE_CDN = "https://unpkg.com/firacode/distr/fira_code.css"
    doc.head.add(tags.link(rel="stylesheet", href=FIRA_CODE_CDN))

    pygments_css = FORMATTER.get_style_defs('.highlight')
    doc.head.add(tags.style(pygments_css, type="text/css"))

    for t in gen_html(annotated):
        doc.body.add(t)

    with open("{}.html".format(fname), mode="w") as out:
        out.write(doc.render(pretty=False))

WRITERS = {'json': write_json, 'html': write_html, 'webpage': write_webpage}

def main():
    args = parse_arguments()

    global DEBUG
    DEBUG = args.debug

    for fname, chunks in args.input:
        annotated = annotate(chunks)
        WRITERS[args.writer](fname, annotated)

if __name__ == '__main__':
    main()
