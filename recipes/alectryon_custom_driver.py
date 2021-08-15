#!/usr/bin/env python3
"""
This is an example of a custom driver: it exposes the same interface as
Alectryon's usual CLI, but it sets the internal parameter pp_margin of SerAPI
to a different value, and it sets up all sorts of custom highlighting.

See ``custom_highlighting.v`` for examples of what it can do.  The following
command is just a sanity test::

   $ python alectryon_custom_driver.py --version | grep -o Alectryon > alectryon_custom_driver.out
       # Custom driver; produces ‘alectryon_custom_driver.out’
"""

import sys
from os.path import join, dirname

## Set up the Python path (not needed if installing from Pip)

root = join(dirname(__file__), "..")
sys.path.insert(0, root)

## Tweak a setting that is not exposed on the command line.

from alectryon.serapi import SerAPI
SerAPI.DEFAULT_PP_ARGS['pp_margin'] = 55

## Teach the Coq lexer to highlight embedded C code

# Create a lexer that highlights C code within ``C:{{ … }}`` blocks, Coq
# comments as Markdown, and a custom mini-language inside ``calc:()`` blocks
# using a custom lexer.

# Step 1: imports
import re
from pygments import token
from pygments.lexer import RegexLexer, bygroups, using, regex_opt
from pygments.lexers.c_cpp import CLexer
from pygments.lexers.markup import MarkdownLexer

# Step 2 (for Markdown in comments): make a custom lexer that changes ``Text``
# tokens into ``Comment``.

class MarkdownInComments(MarkdownLexer):
    def get_tokens_unprocessed(self, text, **kwargs): # pylint: disable=arguments-differ
        for idx, t, v in super().get_tokens_unprocessed(text, **kwargs):
            t = token.Comment if t in (token.Text, token.Whitespace) else t
            yield idx, t, v

# Step 3: Define a lexer that highlights Markdown, C, and a custom mini language
# within certain bounds and tags everything else as ``Other``.

class EmbeddedLexer(RegexLexer):
    name = 'EmbeddedC'
    aliases, filenames = [], []
    flags = re.DOTALL
    tokens = {
        'root': [
            ('(C)(:[{][{])(.+?)([}][}])',
             bygroups(token.Keyword, token.Operator, using(CLexer), token.Operator)),
            ('([(][*])(.+?)([*][)])', # nested comments left as an exercise
             bygroups(token.Comment, using(MarkdownInComments), token.Comment)),
            ('(calc)(:[(])',
             bygroups(token.Keyword, token.Operator), ('#push', 'minilang')),
            ('.', token.Other), # ← This indicates the "host" language
        ],
        'minilang': [
            ("[(]", token.Operator, '#push'),
            ("[)]", token.Operator, '#pop'),
            (regex_opt("add sub div mul".split()), token.Keyword),
            ("[0-9]+", token.Number),
            ("[a-zA-Z0-9_]+", token.Name.Variable),
            (".", token.Text),
        ]
    }

# Step 4: Embed all these domain-specific lexers into a host Coq lexer.

from pygments.lexer import DelegatingLexer
from alectryon.pygments_lexer import CoqLexer

class CustomLexer(DelegatingLexer, CoqLexer):
    name = 'Coq'
    def __init__(self, **options):
        super().__init__(CoqLexer, EmbeddedLexer, **options)

# Step 5: Replace Alectryon's usual Coq lexer with our custom one.  Note how the
# replacement inherits from CoqLexer to not confuse Alectryon.

import alectryon.pygments_lexer
alectryon.pygments_lexer.CoqLexer = CustomLexer

## Run Alectryon's usual CLI

from alectryon.cli import main

if __name__ == "__main__":
    main()
