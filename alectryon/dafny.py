# Copyright © 2022 Clément Pit-Claudel
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

from .lsp import LSPDriver

class DafnyLSP(LSPDriver):
    BIN = "c:/Program Files/LLVM/bin/clangd.exe"
    NAME = "Dafny LSP Server"

    CLI_ARGS = ()
    REPL_ARGS = () # ("--stdio",) # ("--documents:verify=never", "--verifier:timelimit=30")
    VERSION_ARGS = ()

    ID = "dafny_lsp"
    LSP_LANGUAGE_ID = LANGUAGE = "dafny"

    LSP_TYPE_MAP = {
        **LSPDriver.LSP_TYPE_MAP,
        ("string", "documentation"): "String.Doc",
        ("comment", "documentation"): "Comment.Special",
        ("macro",): "Name.Builtin.Pseudo", # Special
        ("modifier",): "Keyword.Declaration",
        ("keyword", "declaration"): "Keyword.Declaration", # Declaration
        ("keyword", "documentation"): "Keyword.Reserved", # Specification
        ("keyword", "defaultLibrary", "documentation"): "Keyword.Reserved", # Assertion
        ("function", "defaultLibrary"): "Name.Builtin", # Builtin
        ("macro", "defaultLibrary"): "Name.Function.Magic", # Macro
        ("number", "defaultLibrary"): "Literal", # Constant

        ("class", "declaration"): "Name.Class", # Value types an reference types are ≠ colors
        ("type", "declaration"): "Keyword.Type",
        ("type", "defaultLibrary"): "Keyword.Type", # Comprehension

        ("parameter", "declaration", "readonly"): "Name.Variable", # FIXME
        ("parameter", "readonly"): "Name.Variable",

        ("function", "definition"): "Name.Function",
        ("function", "declaration"): "Name.Function",
        ("method", "definition"): "Name.Function",
        ("method", "declaration"): "Name.Function",
        ("property", "definition"): "Name.Variable.Instance",
        ("property", "declaration"): "Name.Variable.Instance",
    }
