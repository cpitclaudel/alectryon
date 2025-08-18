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

from collections.abc import Iterable

from .core import Document, Fragment, Positioned, Text
from .tokens import LSPClientSemanticTokensMixin, TokenizedStr
from .lsp import LSPClient, LSPDocument, LSPDriver, LSPFile

class DafnyClient(LSPClientSemanticTokensMixin, LSPClient):
    LANGUAGE_ID = "dafny"

    TOKEN_MAP = {
        **LSPClientSemanticTokensMixin.TOKEN_MAP,
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

class DafnyFile(LSPFile[DafnyClient]):
    def process(self):
        tokens = self.client.get_tokens(self.doc)
        tokenized = TokenizedStr(self.doc.str, tokens, self.client.TOKEN_MAP)
        return [Positioned(0, len(self.doc), Text(tokenized))]

class DafnyLSP(LSPDriver[DafnyClient]):
    BIN = "DafnyLanguageServer"
    NAME = "Dafny LSP Server"

    VERSION_ARGS = ()

    ID = "dafny_lsp"
    LANGUAGE = "dafny"
    AUTOSELECT = True

    CLIENT = DafnyClient

    def _encode(self, chunks: Iterable[str]) -> Document:
        return LSPDocument(chunks, "\n")

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        return DafnyFile(self, document).process()
