# Original theme Copyright 2006-2019 by the Pygments team.
# Modifications Copyright © 2019 Clément Pit-Claudel.
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""
A style inspired by the color palette of the Tango icon theme.

http://tango.freedesktop.org/Tango_Icon_Theme_Guidelines

Butter:     #fce94f     #edd400     #c4a000
Orange:     #fcaf3e     #f57900     #ce5c00
Chocolate:  #e9b96e     #c17d11     #8f5902
Chameleon:  #8ae234     #73d216     #4e9a06
Sky Blue:   #729fcf     #3465a4     #204a87
Plum:       #ad7fa8     #75507b     #5c35cc
Scarlet Red:#ef2929     #cc0000     #a40000
Aluminium:  #eeeeec     #d3d7cf     #babdb6
            #888a85     #555753     #2e3436

Not all of the above colors are used.  Unlike the original `tango` theme for
Pygments, this theme attempts to assign different styles to most tokens.
"""

from pygments.style import Style
from pygments.token import Keyword, Name, Comment, String, Error, \
     Number, Operator, Generic, Whitespace, Punctuation, Other, Literal

class TangoSubtleStyle(Style):
    """
    A style inspired by the color palette of the Tango icon theme.
    """

    background_color = "none"
    default_style = ""

    styles = {
        Whitespace:                "underline #d3d7cf",      # class: 'w'
        Error:                     "#a40000 border:#cc0000", # class: 'err'
        Other:                     "#2e3436",                # class 'x'

        Comment:                   "italic #555753",         # class: 'c'
        Comment.Hashbang:          "italic bold #555753",    # class: 'cm'
        Comment.Multiline:         "italic #555753",         # class: 'cm'
        Comment.Preproc:           "italic #3465a4",         # class: 'cp'
        Comment.Single:            "italic #555753",         # class: 'c1'
        Comment.Special:           "italic bold #3465a4",    # class: 'cs'

        Keyword:                   "#8f5902",                # class: 'k'
        Keyword.Constant:          "bold #204a87",           # class: 'kc'
        Keyword.Declaration:       "bold #4e9a06",           # class: 'kd'
        Keyword.Namespace:         "bold #4e9a06",           # class: 'kn'
        Keyword.Pseudo:            "#204a87",                # class: 'kp'
        Keyword.Reserved:          "#8f5902",                # class: 'kr'
        Keyword.Type:              "#204a87",                # class: 'kt'

        Operator:                  "#000000",                # class: 'o'
        Operator.Word:             "#8f5902",                # class: 'ow'

        Punctuation:               "#000000",                # class: 'p'

        Name:                      "#000000",                # class: 'n'
        Name.Attribute:            "#c4a000",                # class: 'na'
        Name.Builtin:              "#75507b",                # class: 'nb'
        Name.Builtin.Pseudo:       "#5c35cc",                # class: 'bp'
        Name.Class:                "#204a87",                # class: 'nc'
        Name.Constant:             "#ce5c00",                # class: 'no'
        Name.Decorator:            "bold #3465a4",           # class: 'nd'
        Name.Entity:               "underline #c4a000",      # class: 'ni'
        Name.Exception:            "#cc0000",                # class: 'ne'
        Name.Function:             "#a40000",                # class: 'nf'
        Name.Label:                "bold #3465a4",           # class: 'nl'
        Name.Namespace:            "#000000",                # class: 'nn'
        Name.Other:                "#000000",                # class: 'nx'
        Name.Tag:                  "#a40000",                # class: 'nt'
        Name.Variable:             "#ce5c00",                # class: 'nv'
        Name.Variable.Class:       "#ce5c00",                # class: 'vc'
        Name.Variable.Global:      "underline #ce5c00",      # class: 'vg'
        Name.Variable.Instance:    "#ce5c00",                # class: 'vi'

        Number:                    "#2e3436",                # class: 'm'
        Number.Float:              "#2e3436",                # class: 'mf'
        Number.Hex:                "#2e3436",                # class: 'mh'
        Number.Integer:            "#2e3436",                # class: 'mi'
        Number.Integer.Long:       "#2e3436",                # class: 'il'
        Number.Oct:                "#2e3436",                # class: 'mo'

        Literal:                   "#2e3436",                # class: 'l'
        Literal.Date:              "#2e3436",                # class: 'ld'

        String:                    "#ad7fa8",                # class: 's'
        String.Backtick:           "#ad7fa8",                # class: 'sb'
        String.Char:               "bold #ad7fa8",           # class: 'sc'
        String.Doc:                "#ad7fa8",                # class: 'sd'
        String.Double:             "#ad7fa8",                # class: 's2'
        String.Escape:             "bold #ad7fa8",           # class: 'se'
        String.Heredoc:            "underline #ad7fa8",      # class: 'sh'
        String.Interpol:           "#ce5c00",                # class: 'si'
        String.Other:              "#ad7fa8",                # class: 'sx'
        String.Regex:              "#ad7fa8",                # class: 'sr'
        String.Single:             "#ad7fa8",                # class: 's1'
        String.Symbol:             "#8f5902",                # class: 'ss'

        Generic:                   "#000000",                # class: 'g'
        Generic.Deleted:           "#a40000",                # class: 'gd'
        Generic.Emph:              "italic #000000",         # class: 'ge'
        Generic.Error:             "#a40000",                # class: 'gr'
        Generic.Heading:           "bold #a40000",           # class: 'gh'
        Generic.Inserted:          "#4e9a06",                # class: 'gi'
        Generic.Output:            "italic #000000",         # class: 'go'
        Generic.Prompt:            "#8f5902",                # class: 'gp'
        Generic.Strong:            "bold #000000",           # class: 'gs'
        Generic.Subheading:        "bold #000000",           # class: 'gu'
        Generic.Traceback:         "italic #000000",         # class: 'gt'
    }
