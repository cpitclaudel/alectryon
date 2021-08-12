
"""
A pygments lexer for Elpi.
"""

from pygments.lexer import RegexLexer, default, words, bygroups, include, inherit
from pygments.regexopt import regex_opt, regex_opt_inner
from pygments.token import \
    Text, Comment, Operator, Keyword, Name, String, Number

class ElpiLexer(RegexLexer):
    """
    For the `Elpi <http://github.com/LPCIC/elpi>`_ programming language.

    .. versionadded:: 1.0
    """

    name = 'Elpi'
    aliases = ['elpi']
    filenames = ['*.elpi']
    mimetypes = ['text/x-elpi']
    
    lcase_re = r"[a-z]"
    ucase_re = r"[A-Z]"
    digit_re = r"[0-9]"
    schar2_re = r"(\+|\*|/|\^|<|>|`|'|\?|@|#|~|=|&|!)"
    schar_re = r"({}|-|\$|_)".format(schar2_re)
    idchar_re = r"({}|{}|{}|{})".format(lcase_re,ucase_re,digit_re,schar_re)
    idcharstarns_re = r"({}+|(?=\.[a-z])\.{}+)".format(idchar_re,idchar_re)
    symbchar_re = r"({}|{}|{}|{}|:)".format(lcase_re, ucase_re, digit_re, schar_re)
    constant_re = r"({}{}*|{}{}*|{}{}*|_{}+)".format(ucase_re, idchar_re, lcase_re, idcharstarns_re,schar2_re, symbchar_re,idchar_re)
    symbol_re=r"(,|<=>|->|:-|;|\?-|->|&|=>|as|<|=<|=|==|>=|>|i<|i=<|i>=|i>|is|r<|r=<|r>=|r>|s<|s=<|s>=|s>|@|::|`->|`:|`:=|\^|-|\+|i-|i\+|r-|r\+|/|\*|div|i\*|mod|r\*|~|i~|r~)"
    escape_re=r"\(({}|{})\)".format(constant_re,symbol_re)
    const_sym_re = r"({}|{}|{})".format(constant_re,symbol_re,escape_re)

    tokens = {
        'root': [ include('elpi') ],

        'elpi': [

            include('_elpi-comment'),

            (r"(:before|:after|:if|:name)(\s*)(\")",bygroups(Keyword.ElpiMode,Text,String.Double),'elpi-string'),
            (r"(:index)(\s*\()",bygroups(Keyword.ElpiMode,Text),'elpi-indexing-expr'),
            (r"(external pred|pred)(\s+)({})".format(const_sym_re),bygroups(Keyword.ElpiKeyword,Text,Name.ElpiFunction),'elpi-pred-item'),
            (r"(external type|type)(\s+)(({}(,\s*)?)+)".format(const_sym_re),bygroups(Keyword.ElpiKeyword,Text,Name.ElpiFunction),'elpi-type'),
            (r"(kind)(\s+)(({}|,)+)".format(const_sym_re),bygroups(Keyword.ElpiKeyword,Text,Name.ElpiFunction),'elpi-type'),
            (r"(typeabbrev)(\s+)({})".format(const_sym_re),bygroups(Keyword.ElpiKeyword,Text,Name.ElpiFunction),'elpi-type'),
            (r"(accumulate)(\s+)(\")",bygroups(Keyword.ElpiKeyword,Text,String.Double),'elpi-string'),
            (r"(accumulate|shorten|namespace|local)(\s+)({})".format(constant_re),bygroups(Keyword.ElpiKeyword,Text,Text)),
            (r"(pi|sigma)(\s+)([a-zA-Z][A-Za-z0-9_ ]*)(\\)",bygroups(Keyword.ElpiKeyword,Text,Name.ElpiVariable,Text)),
            (r"rule",Keyword.ElpiKeyword),
            (r"(constraint)(\s+)(({}(\s+)?)+)".format(const_sym_re),bygroups(Keyword.ElpiKeyword,Text,Name.ElpiFunction)),

            (r"(?=[A-Z_]){}".format(constant_re),Name.ElpiVariable),
            (r"(?=[a-z_]){}\\".format(constant_re),Name.ElpiVariable),
            (r"_",Name.ElpiVariable),
            (r"({}|!|=>|;)".format(symbol_re),Keyword.ElpiKeyword),
            (constant_re,Text),
            (r"\[|\]|\||=>",Keyword.ElpiKeyword),
            (r'"', String.Double, 'elpi-string'),
            (r'`', String.Double, 'elpi-btick'),
            (r'\'', String.Double, 'elpi-tick'),
            (r'\{[^\{]', Text, 'elpi-spill'),
            (r"\(",Text,'elpi-in-parens'),
            (r'\d[\d_]*', Number.ElpiInteger),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.ElpiFloat),
            (r"[+\*-/\^]", Operator),
        ],
        '_elpi-comment': [
            (r'%[^\n]*\n',Comment),
            (r'/\*',Comment,'elpi-multiline-comment'),
            (r"\s+",Text),
        ],
        'elpi-multiline-comment': [
            (r'\*/',Comment,'#pop'),
            (r'.',Comment)
        ],
        'elpi-indexing-expr':[
            (r'[0-9 _]+',Number.ElpiInteger),
            (r'\)',Text,'#pop'),
        ],
        'elpi-type': [
            (r"(ctype\s+)(\")",bygroups(Keyword.Type,String.Double),'elpi-string'),
            (r'->',Keyword.Type),
            (constant_re,Keyword.Type),
            (r"\(|\)",Keyword.Type),
            (r"\.",Text,'#pop'),
            include('_elpi-comment'),
        ],
        'elpi-pred-item': [
            (r"[io]:",Keyword.ElpiMode,'elpi-ctype'),
            (r"\.",Text,'#pop'),
            include('_elpi-comment'),
        ],
        'elpi-ctype': [
            (r"(ctype\s+)(\")",bygroups(Keyword.Type,String.Double),'elpi-string'),
            (constant_re,Keyword.Type),
            (r"\(|\)",Keyword.Type),
            (r",",Text,'#pop'),
            (r"\.",Text,'#pop:2'),
            include('_elpi-comment'),
        ],
        'elpi-btick': [
            (r'[^` ]+', String.Double),
            (r'`', String.Double, '#pop'),
        ],
        'elpi-tick': [
            (r'[^\' ]+', String.Double),
            (r'\'', String.Double, '#pop'),
        ],
        'elpi-string': [
            (r'[^\"]+', String.Double),
            (r'"', String.Double, '#pop'),
        ],
        'elpi-spill': [
            (r'\{[^\{]', Text, '#push'),
            (r'\}[^\}]', Text, '#pop'),
            include('elpi'),
        ],
        'elpi-in-parens': [
            (r"\(", Operator, '#push'),
            (r"\)", Operator, '#pop'),
            include('elpi'),
        ],

    }

from .pygments_lexer import CoqLexer

class CoqLexer(CoqLexer, ElpiLexer):

    tokens = {
      'root': [
            # No clue what inherit would do here, so we copy Coq's ones
            include('_basic'),
            include('_vernac'),
            include('_keywords'),
            include('_other'),
      ],
      '_quotations': [
            (r"lp:\{\{",Text, 'elpi'),
            (r"(lp:)([A-Za-z_0-9']+)",bygroups(Text, Name.ElpiVariable)),
            (r"(lp:)(\()([A-Z][A-Za-z_0-9']*)([a-z0-9 ]+)(\))",bygroups(Text,Text,Name.ElpiVariable,Text,Text)),
            inherit
      ],
      'antiquotation': [
            (r"\}\}",Text,'#pop'),
            inherit
      ],
      'elpi': [
            (r"\}\}",Text,'#pop'),
            (r"global|sort|app|fun|let|prod|match|fix", Keyword.ElpiKeyword),
            (r"\{\{",Text,'antiquotation'), # back to Coq
            inherit
      ],

    }

__all__ = ["ElpiLexer","CoqLexer"]
