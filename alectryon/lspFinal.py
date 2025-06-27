# Copyright © 2022, 2025 Flavien Jacquerod, Clément Pit-Claudel
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

from typing import Any, ClassVar, Dict, Generic, Optional, Self, Type, TypeVar

import json
import os
import re
import dataclasses
from pathlib import Path
from subprocess import Popen

from .core import DriverInfo, PopenDriver, debug as core_debug

JSON = Dict[str, Any]

class LSPServerMessage:
    """Base class for all LSP messages"""
    @classmethod
    def from_json(cls, data: Dict) -> "LSPServerMessage":
        idx = data.get("id")
        method = data.get("method")

        if method is not None:
            if idx is not None:
                return LSPServerRequest.from_json(data)
            else:
                return LSPServerNotification.from_json(data)
        else:
            if "error" in data:
                raise LSPServerError.from_json(data).exn
            else:
                return LSPServerResponse.from_json(data)

    JRPC_HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    @staticmethod
    def from_stream(stream) -> "LSPServerMessage":
        """Read and parse an LSP server message from a stream."""
        line, length = None, None
        while line not in ("", "\r\n"):
            line = stream.readline().decode("utf-8")
            core_debug(repr(line), "<< ")
            header = LSPServerMessage.JRPC_HEADER_RE.match(line)
            if header:
                length = int(header.group("len"))

        if line == "":
            raise EOFError("Connection closed")
        if length is None:
            raise ValueError("No Content-Length header")

        response = stream.read(length)
        if len(response) != length:
            raise ValueError("Truncated response")

        resp = response.decode("utf-8")
        core_debug(resp, "<< ")
        data = json.loads(resp)

        return LSPServerMessage.from_json(data)

@dataclasses.dataclass
class LSPClientMessage:
    client: "LSPClient"

    def json(self) -> JSON:
        raise NotImplementedError

    def serialize(self) -> bytes:
        js = json.dumps(self.json(), indent=1).replace("\n", "\r\n") + "\r\n"
        header = f"Content-Length: {len(js)}\r\n\r\n"
        return header.encode("utf-8") + js.encode("utf-8")

    def send(self):
        raise NotImplementedError

class LSPClientQuery(LSPClientMessage):
    """Base class for LSP requests and notifications."""
    METHOD: ClassVar[str]

    @property
    def params(self) -> dict[str, Any]:
        return {}

    def process_message(self, message: LSPServerMessage):
        if isinstance(message, LSPServerRequest):
            LSPClientMethodNotFoundError(self.client, message.idx).send()

    def json(self) -> JSON:
        """Serialize this query."""
        return {
            "jsonrpc": "2.0",
            "method": self.METHOD,
            "params": self.params
        }

    def send(self) -> Self:
        return self.client.send_and_process(self)

    @property
    def done(self) -> bool:
        """Check whether this query is done processing server messages."""
        raise NotImplementedError

@dataclasses.dataclass
class LSPClientRequest(LSPClientQuery):
    def __post_init__(self):
        self.idx: int = self._gensym()
        self._result: Optional[JSON] = None
        self._done = False

    GENSYM: ClassVar[int] = -1

    @classmethod
    def _gensym(cls):
        cls.GENSYM += 1
        return cls.GENSYM

    def json(self) -> JSON:
        return {**super().json(), "id": self.idx}

    def process_message(self, message: LSPServerMessage):
        super().process_message(message)
        if isinstance(message, LSPServerResponse) and message.idx == self.idx:
            self._result = message.result
            self._done = True
        elif isinstance(message, LSPServerError) and message.idx == self.idx:
            raise message.exn

    @property
    def done(self) -> bool:
        return self._done

    @property
    def result(self) -> JSON:
        assert self._result
        return self._result

@dataclasses.dataclass
class LSPServerRequest(LSPServerMessage):
    idx: int
    method: str
    params: dict[str, Any]

    @classmethod
    def from_json(cls, data: Dict) -> "LSPServerRequest":
        return cls(data["id"], data["method"], data.get("params", {}))

class LSPClientNotification(LSPClientQuery):
    @property
    def params(self) -> dict[str, Any]:
        return {}

    @property
    def done(self) -> bool:
        return True

@dataclasses.dataclass
class LSPServerNotification(LSPServerMessage):
    method: str
    params: dict[str, Any]

    @classmethod
    def from_json(cls, data: JSON) -> "LSPServerNotification":
        return cls(data["method"], data.get("params", {}))

class LSPServerNotifications:
    PUBLISH_DIAGNOSTICS = "textDocument/publishDiagnostics"

@dataclasses.dataclass
class LSPServerResponse(LSPServerMessage):
    def __init__(self, idx: int, result: JSON):
        self.idx = idx
        self.result = result

    @classmethod
    def from_json(cls, data: Dict) -> "Self":
        return cls(data["id"], data.get("result", {}))

class LSPClientResponse(LSPServerMessage):
    def __init__(self, idx: int, result: JSON):
        self.idx = idx
        self.result = result

    def json(self) -> JSON:
        """Convert response to JSON for sending"""
        return {
            "jsonrpc": "2.0",
            "id": self.idx,
            "result": self.result
        }

class LSPServerException(Exception):
    def __init__(self, message: str, code: int):
        super().__init__(message)
        self.code = code

@dataclasses.dataclass
class LSPServerError(LSPServerMessage):
    idx: int
    code: int
    message: str

    @property
    def exn(self) -> LSPServerException:
        raise LSPServerException(self.message, self.code)

    @classmethod
    def from_json(cls, data: Dict) -> "LSPServerError":
        error_info = data["error"]
        return cls(data["id"], error_info["code"], error_info["message"])

@dataclasses.dataclass
class LSPClientError(LSPClientMessage):
    idx: int
    CODE: ClassVar[int]
    MESSAGE: ClassVar[str]

    def json(self) -> JSON:
        return {
            "jsonrpc": "2.0",
            "id": self.idx,
            "error": { "code": self.CODE, "message": self.MESSAGE }
        }

    def send(self):
        self.client.send_message(self)

class LSPClientMethodNotFoundError(LSPClientError):
    CODE = -32601
    MESSAGE = "This client does not support server requests."

class LSPClientSemanticTokensRequest(LSPClientRequest):
    METHOD = "textDocument/semanticTokens/full"

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

class LSPClientInitializeRequest(LSPClientRequest):
    METHOD = "initialize"

    CLIENT_NAME = "LSPClient"
    CAPABILITIES = {
        "workspace": { "configuration": False },
        "textDocument": {
             "workspace": {
                 "configuration": False,
             },
             "textDocument": {
                 "semanticTokens": {
                     "requests": {"range": False, "full": True},
                     "tokenTypes": list(LSPClientSemanticTokensRequest.TOKEN_TYPES),
                     "tokenModifiers": list(LSPClientSemanticTokensRequest.TOKEN_MODIFIERS),
                     "formats": ['relative'],
                     "overlappingTokenSupport": False,
                     "multilineTokenSupport": True,
                     "serverCancelSupport": False,
                     "augmentsSyntaxTokens": False,
                 }
             }
         }
    }

    @property
    def params(self):
        return {
            "processId": __import__('os').getpid(),
            "clientInfo": {"name": self.CLIENT_NAME, "version": "1.0.0"},
            "rootUri": Path(os.getcwd()).as_uri(),
            "capabilities": self.CAPABILITIES
        }

    @property
    def driver_info(self):
        assert self.done
        info = self.result.get("serverInfo")
        return DriverInfo(info["name"], info.get("version", "?")) if info else None

class LSPInitializedNotification(LSPClientNotification):
    METHOD = "initialized"

@dataclasses.dataclass
class LSPClientDidOpenNotification(LSPClientNotification):
    METHOD = "textDocument/didOpen"

    languageId: str
    uri: str
    text: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "languageId": self.languageId,
                                   "version": 0, "text": self.text } }

class LSPClientShutdownRequest(LSPClientRequest):
    METHOD = "shutdown"

class LSPClientExitNotification(LSPClientNotification):
    METHOD = "exit"

class LSPClient:
    LANGUAGE_ID: ClassVar[str]

    def __init__(self, repl: Popen):
        self.repl = repl
        self.driver_info: Optional[DriverInfo] = None
        self.init()

    def receive_message(self) -> LSPServerMessage:
        return LSPServerMessage.from_stream(self.repl.stdout)

    def send_message(self, query: LSPClientMessage) -> None:
        bs = query.serialize()
        core_debug(bs, ">> ")
        self.repl.stdin.write(bs)
        self.repl.stdin.flush()

    T = TypeVar("T", bound=LSPClientQuery)

    def send_and_process(self, query: T) -> T:
        self.send_message(query)
        while not query.done:
            query.process_message(self.receive_message())
        return query

    def init(self):
        self.driver_info = LSPClientInitializeRequest(self).send().driver_info
        LSPInitializedNotification(self).send()

    def kill(self):
        LSPClientShutdownRequest(self).send()
        LSPClientExitNotification(self).send()

    def open(self, uri: str, contents: str) -> None:
        LSPClientDidOpenNotification(self, self.LANGUAGE_ID, uri, contents).send()

T = TypeVar("T", bound=LSPClient)
class LSPDriver(PopenDriver, Generic[T]):
    CLIENT: Type[T]
    _client: Optional[T] = None

    def version_info(self) -> DriverInfo:
        with self:
            return self._client.driver_info or DriverInfo(self.NAME, "?")

    def reset(self):
        super().reset()
        assert self.repl
        self._client = self.CLIENT(self.repl)

    def kill(self):
        if self._client:
            self._client.kill()
        super().kill()

    @property
    def uri(self):
        path = self.fpath.with_name("alectryon_temp") if self.fpath.name == "-" else self.fpath
        return path.absolute().as_uri()

    @property
    def client(self):
        assert self._client
        return self._client
