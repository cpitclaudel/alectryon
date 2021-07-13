import re

SEXP_SPECIAL = re.compile(rb'[ ()"]')
STR_SPECIAL = re.compile(rb'[\\"]')
OPEN, CLOSE, ESCAPE, QUOTE = map(ord, r'()\"')

STRING_QUOTES = [(b'\\', b'\\'), (b'"', b'"'), (b'\r', b'r'), (b'\n', b'n'),
                 (b'\b', b'b'), (b'\f', b'f'), (b'\t', b't')]

STRING_QUOTE_RE = re.compile(rb'[\\"\r\n\b\f\t]')
STRING_UNQUOTE_RE = re.compile(rb'\\[\\"rnbft]')
STRING_QUOTE_TBL = {raw[0]: b"\\" + quoted for raw, quoted in STRING_QUOTES}
STRING_UNQUOTE_TBL = {quoted[0]: raw for raw, quoted in STRING_QUOTES}

def unescape_1(m):
    return STRING_UNQUOTE_TBL[m.string[m.start() + 1]]

def unescape(bs):
    return STRING_UNQUOTE_RE.sub(unescape_1, bs)

def escape_1(m):
    return STRING_QUOTE_TBL[m.string[m.start()]]

def escape(bs):
    return STRING_QUOTE_RE.sub(escape_1, bs)

def tostr(bs):
    return unescape(bs).decode('utf-8')

def tokenize_str(view, start, str_special=STR_SPECIAL):
    pos = start
    while True:
        m = str_special.search(view, pos)
        if m is None:
            MSG = "Unterminated string: {!r}@{}."
            raise ValueError(MSG.format(view, start))
        if view[m.start()] == ESCAPE:
            pos = m.end() + 1
        else:
            yield view[start:m.start()]
            return m.end()

def tokenize(view, sexp_special=SEXP_SPECIAL):
    pos = 0
    while True:
        m = sexp_special.search(view, pos)
        if m is None:
            break
        mstart, mend = m.span()
        if mstart > pos:
            yield view[pos:mstart]
        pos = mend
        special = view[mstart]
        if special in (OPEN, CLOSE):
            yield special
        elif special == QUOTE:
            pos = yield from tokenize_str(view, pos)
    if len(view) > pos:
        yield view[pos:]

def parse(tokens):
    top = []
    stack = []
    for tok in tokens:
        if tok is OPEN:
            new = []
            top.append(new)
            stack.append(top)
            top = new
        elif tok is CLOSE:
            top = stack.pop()
        else:
            top.append(tok)
    return top[0]

class ParseError(Exception):
    pass

def load(bs):
    try:
        return parse(tokenize(bs))
    except IndexError:
        raise ParseError()

def unparse(sexp, buf):
    stack = [sexp]
    while stack:
        top = stack.pop()
        if isinstance(top, list):
            buf.append(OPEN)
            stack.append(CLOSE)
            stack.extend(reversed(top))
        elif isinstance(top, bytes):
            buf.append(QUOTE)
            buf.extend(top)
            buf.append(QUOTE)
        else:
            assert isinstance(top, int)
            buf.append(top)

def dump(sexp):
    buf = bytearray()
    unparse(sexp, buf)
    return buf
