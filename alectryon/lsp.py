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

from typing import Any, Dict, Iterable, Iterator, IO, List, Tuple, Union, \
    Optional, NamedTuple

import json
import os
import re
from enum import Enum
from pathlib import Path
from subprocess import Popen

from .core import debug, Document, DriverInfo, Position, REPLDriver, Text, Fragment
from .tokens import Range, Token, Tokens, TokenizedStr

class LSPRequest(Enum):
    INITIALIZE = "initialize"
    SHUTDOWN = "shutdown"
    SEMANTIC_TOKENS_FULL = "textDocument/semanticTokens/full"
LSP_REQUESTS = set(r.value for r in LSPRequest)

class LSPNotification(Enum):
    INITIALIZED = "initialized"
    DID_OPEN = "textDocument/didOpen"
    EXIT = "exit"
LSP_NOTIFICATIONS = set(n.value for n in LSPNotification)

JSON = Dict[str, Any]
LSPMethod = Union[LSPRequest, LSPNotification, str]

class LSPException(ValueError):
    pass

class LSPError(NamedTuple):
    idx: int
    code: int
    message: str

    def json(self) -> JSON:
        return {
            "jsonrpc": "2.0",
            "id": self.idx,
            "error": { "code": self.code, "message": self.message },
        }

class LSPResponse(NamedTuple):
    idx: int
    result: JSON

    def json(self) -> JSON:
        return {
            "jsonrpc": "2.0",
            "id": self.idx,
            "result": self.result,
        }

class LSPQuery(NamedTuple):
    idx: Optional[int]
    method: LSPMethod
    params: JSON

    @property
    def is_request(self):
        return self.idx is not None

    def json(self) -> JSON:
        return {
            "jsonrpc": "2.0",
            "method": getattr(self.method, "value", self.method),
            "params": self.params,
            **({"id": self.idx} if self.is_request else {})
        }

LSPMessage = Union[LSPError, LSPResponse, LSPQuery]

class LSPParser:
    JRPC_HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    @staticmethod
    def serialize(msg: LSPMessage) -> bytes:
        js = json.dumps(msg.json(), indent=1).replace("\n", "\r\n") + "\r\n"
        header = "Content-Length: {}\r\n\r\n".format(len(js))
        return header.encode("utf-8") + js.encode("utf-8")

    @staticmethod
    def parse_lsp_method(m: str) -> LSPMethod:
        if m in LSP_NOTIFICATIONS:
            return LSPNotification(m)
        if m in LSP_REQUESTS:
            return LSPRequest(m)
        return m

    @staticmethod
    def from_json(js: JSON) -> "LSPMessage":
        idx = int(js["id"]) if "id" in js else None
        method = js.get("method")
        if method is not None:
            return LSPQuery(idx, LSPParser.parse_lsp_method(method), js["params"])
        if "result" not in js:
            raise LSPException("LSP Error: {!r}".format(js["error"]))
        assert idx is not None
        return LSPResponse(idx, js["result"])

    @staticmethod
    def from_stream(stream: IO[bytes]) -> "LSPMessage":
        line, length = None, None
        while line not in ("", "\r\n"):
            line = stream.readline().decode("utf-8")
            debug(repr(line), '<< ')
            header = LSPParser.JRPC_HEADER_RE.match(line)
            if header:
                length = int(header.group("len"))
        if line == "":
            raise EOFError
        if length is None:
            MSG = ("Unexpected output: {!r}, use --debug for a trace.".format(line) +
                   "If --debug doesn't help, check the LSP server's logs.")
            raise LSPException(MSG)
        response: bytes = stream.read(length)
        if len(response) != length:
            raise LSPException(f"Truncated response: {response!r}")
        resp = response.decode("utf-8")
        debug(resp, "<< ")
        return LSPParser.from_json(json.loads(resp))

class LSPTokenLegend:
    def __init__(self, doc: Document, lsp_legend: JSON):
        self.doc = doc
        self.types = lsp_legend["tokenTypes"]
        self.modifiers = lsp_legend["tokenModifiers"]
        self.modifiers_dict: Dict[int, Tuple[str, ...]] = {}

    def resolve_mods(self, imods: int) -> Tuple[str, ...]:
        mods: Optional[Tuple[str, ...]] = self.modifiers_dict.get(imods)
        if mods is None:
            mods = self.modifiers_dict[imods] = tuple(sorted(
                self.modifiers[i]
                for i, c in enumerate(bin(imods)[:1:-1], 0)
                if c == '1'
            ))
        return mods

    def resolve_one(self, l: int, c: int, length: int, itype: int, imods: int) -> Token:
        typ = self.types[itype]
        mods = self.resolve_mods(imods)
        start = self.doc.pos2offset(l, c)
        return Token(Range(start, start + length), (typ, *mods))

    def resolve(self, tokens: Iterable[int]) -> Iterator[Token]:
        l, c = 1, 0
        groups = zip(*([iter(tokens)] * 5))
        for dl, dc, length, itype, imods in groups:  # type: ignore
            l, c = l + dl, (dc if dl != 0 else c + dc)
            yield self.resolve_one(l, c, length, itype, imods)

class LSPAdapter:
    def __init__(self, client_name: str, language_id: str):
        self.language_id = language_id
        self.client_name = client_name

    TOKEN_TYPES: Dict[str, str] = {
        "namespace": "Name.Namespace",
        "type": "Keyword.Type",
        "class": "Name.Class",
        "enum": "Name.Class",
        "interface": "Name.Class",
        "struct": "Name.Class",
        "typeParameter": "Name.Entity",
        "parameter": "Name.Variable",
        "variable": "Name.Variable",
        "property": "Name.Variable.Instance",
        "enumMember": "Name.Constant",
        "event": "Name.Class",
        "function": "Name.Function",
        "method": "Name.Function",
        "macro": "Name.Function",
        "keyword": "Keyword",
        "modifier": "Keyword",
        "comment": "Comment",
        "string": "String",
        "number": "Number",
        "regexp": "String.Regex",
        "operator": "Operator"
    }

    TOKEN_MODIFIERS = {
        'declaration', 'definition', 'readonly', 'static', 'deprecated',
        'abstract', 'async', 'modification', 'documentation', 'defaultLibrary'
    }

    def _iter_lsp_initialize(self) -> Iterator[Tuple[LSPMethod, JSON]]:
        yield (LSPRequest.INITIALIZE, {
            "processId": os.getpid(),
            "clientInfo": {"name": self.client_name},
            "rootUri": Path(os.getcwd()).as_uri(),
            "capabilities": {
                "workspace": {
                    "configuration": False,
                },
                "textDocument": {
                    "semanticTokens": {
                        "requests": {"range": False, "full": True},
                        "tokenTypes": list(self.TOKEN_TYPES),
                        "tokenModifiers": list(self.TOKEN_MODIFIERS),
                        "formats": ['relative'],
                        "overlappingTokenSupport": False,
                        "multilineTokenSupport": True,
                        "serverCancelSupport": False,
                        "augmentsSyntaxTokens": False,
                    }
                }
            }
        })
        yield (LSPNotification.INITIALIZED, {})

    @staticmethod
    def _iter_lsp_shutdown():
        yield (LSPRequest.SHUTDOWN, {})
        yield (LSPNotification.EXIT, {})

    def _lsp_query_tokens(self, uri: str, contents: str) -> Iterator[Tuple[LSPMethod, JSON]]:
        yield from self._iter_lsp_initialize()
        yield (LSPNotification.DID_OPEN, {
            "textDocument": {
                "uri": uri,
                "languageId": self.language_id,
                "version": 0,
                "text": contents
            }
        })
        yield (LSPRequest.SEMANTIC_TOKENS_FULL, {
            "textDocument": { "uri": uri }
        })
        yield from self._iter_lsp_shutdown()

    def _lsp_query_version(self):
        yield from self._iter_lsp_initialize()
        yield from self._iter_lsp_shutdown()

    @staticmethod
    def _iter_lsp(transcript: Iterable[Tuple[LSPMethod, JSON]]) -> Iterator[LSPQuery]:
        for idx, (method, params) in enumerate(transcript):
            yield LSPQuery(idx if isinstance(method, LSPRequest) else None, method, params)

    @staticmethod
    def _write_lsp(repl: Popen, msg: LSPMessage) -> None:
        assert repl.stdin
        bs = LSPParser.serialize(msg)
        debug(bs, '>> ')
        repl.stdin.write(bs)  # type: ignore
        repl.stdin.flush()

    @staticmethod
    def _unsupported(idx: int) -> LSPError:
        return LSPError(idx, code=-32601, # Method not found
                        message="This client does not support server requests.")

    @staticmethod
    def _run_lsp(repl: Popen, trace: Iterable[LSPQuery]) -> Iterator[Tuple[LSPMethod, LSPResponse]]:
        """Collect responses to LSP messages in `trace`."""
        assert repl.stdout
        trace = list(trace)
        for msg in trace:
            LSPAdapter._write_lsp(repl, msg)
            if msg.is_request:
                while True:
                    resp = LSPParser.from_stream(repl.stdout)
                    if isinstance(resp, LSPResponse) and resp.idx == msg.idx:
                        yield (msg.method, resp)
                        break
                    # TODO: Implement the diagnostic request in the server, use it from here.
                    if isinstance(resp, LSPQuery) and resp.is_request:
                        assert resp.idx
                        LSPAdapter._write_lsp(repl, LSPAdapter._unsupported(resp.idx))

    @staticmethod
    def _remove_overlapping(tokens: Iterable[Token]) -> List[Token]:
        """Remove overlapping token from a list of `tokens`.

        Later tokens are preferred over earlier ones, so if two overlapping
        tokens are found the first one is discarded.
        """
        filtered: List[Token] = []
        tokens = sorted(tokens, key=lambda t: t.rng)
        for tok in tokens:
            while filtered and tok.rng.start < filtered[-1].rng.end:
                filtered.pop()
            filtered.append(tok)
        return filtered

    def collect_lsp_info(self, repl: Popen, uri: str, doc: Document) -> Tokens:
        messages = self._iter_lsp(self._lsp_query_tokens(uri, doc.contents))
        tokens: Optional[Iterable[Token]] = None
        token_options: Optional[Dict[str, Any]] = None
        for (method, response) in self._run_lsp(repl, messages):
            if method is LSPRequest.INITIALIZE:
                token_options = response.result["capabilities"].get("semanticTokensProvider")
            # TODO add a case for diagnostics.
            elif method is LSPRequest.SEMANTIC_TOKENS_FULL:
                if token_options is None or not token_options.get("full"):
                    raise LSPException("This LSP server does not support semantic tokens")
                # No early return: must exhaust iterator
                # pylint: disable=unsubscriptable-object
                legend = LSPTokenLegend(doc, token_options["legend"])
                tokens = legend.resolve(response.result["data"])
        assert tokens is not None
        toks = self._remove_overlapping(tokens)
        return Tokens(toks, slice(0, len(toks), None), Range(0, len(doc)))

    def read_driver_info(self, repl: Popen) -> Optional[DriverInfo]:
        messages = self._iter_lsp(self._lsp_query_version())
        for (method, response) in self._run_lsp(repl, messages):
            if method is LSPRequest.INITIALIZE:
                info = response.result.get("serverInfo")
                return DriverInfo(info["name"], info.get("version", "?")) if info else None
        assert False

class LSPDriver(REPLDriver):
    """An base class for Alectryon Drivers talking to an LSP server."""
    ID = "lsp"
    LANGUAGE = "unset!"

    LSP_CLIENT_NAME = "Alectryon"
    LSP_LANGUAGE_ID = "unset!"

    LSP_TYPE_MAP: Dict[Tuple[str, ...], str] = \
        {(typ,): tok for (typ, tok) in LSPAdapter.TOKEN_TYPES.items()}

    @property
    def adapter(self):
        assert self.LSP_LANGUAGE_ID
        return LSPAdapter(self.LSP_CLIENT_NAME, self.LSP_LANGUAGE_ID)

    def version_info(self) -> DriverInfo:
        with self as api:
            assert api.repl
            return self.adapter.read_driver_info(api.repl) \
                or DriverInfo(self.LANGUAGE, "?")

    def collect_lsp_info(self, doc: Document) -> Tokens:
        with self as api:
            assert api.repl
            uri = api.fpath.absolute().as_uri()
            return self.adapter.collect_lsp_info(api.repl, uri, doc)

    def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
        """Annotate chunks using the ``symbols`` command."""
        try:
            doc = Document(chunks, "\n")
            tokens = self.collect_lsp_info(doc)
            type_map: Dict[Tuple[str, ...], str] = self.LSP_TYPE_MAP
            tokenized = TokenizedStr(doc.contents, tokens, type_map)

            return list(doc.recover_chunks([Text(tokenized)]))
        except LSPException as e:
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1).as_range(), level=3)
            return [[Text(c)] for c in chunks]
