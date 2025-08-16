# Copyright © 2022, 2025 Flavien Jaquerod, Clément Pit-Claudel
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

from typing import IO, Any, ClassVar, Dict, Generic, Iterable, Optional, Self, Type, TypeVar, overload

import json
import os
import re
from dataclasses import dataclass, field
from pathlib import Path

from .transforms import coalesce_text
from .core import Document, DriverInfo, EncodedDocument, Fragment, Observer, PopenDriver, Position, Positioned, Range, Text, debug as core_debug, must

JSON = Dict[str, Any]

class LSPServerMessage:
    """Base class for all LSP messages"""
    @classmethod
    def from_json(cls, data: JSON) -> "LSPServerMessage":
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
    def from_stream(stream: IO[bytes]) -> "LSPServerMessage":
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

@dataclass
class LSPClientMessage:
    client: "LSPClient"

    def json(self) -> JSON:
        raise NotImplementedError

    def serialize(self) -> bytes:
        js = json.dumps(self.json(), indent=1).replace("\n", "\r\n") + "\r\n"
        jsb = js.encode("utf-8")
        header = f"Content-Length: {len(jsb)}\r\n\r\n"
        return header.encode("utf-8") + jsb

    def send(self):
        raise NotImplementedError

class LSPClientQuery(LSPClientMessage):
    """Base class for LSP requests and notifications."""
    METHOD: ClassVar[str]

    @property
    def params(self) -> dict[str, JSON]:
        return {}

    def process_notification(self, message: "LSPServerNotification"):
        if message.method in (LSPServerNotifications.SHOW_MESSAGE,
                              LSPServerNotifications.LOG_MESSAGE):
            LSPMessage.of_json(message.params).notify(self.client.driver.observer)

    def process_message(self, message: LSPServerMessage):
        if isinstance(message, LSPServerRequest):
            LSPClientMethodNotFoundError(self.client, message.idx).send()
        elif isinstance(message, LSPServerNotification):
            self.process_notification(message)

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

@dataclass
class LSPClientRequest(LSPClientQuery):
    idx: int = field(init=False)
    result: Optional[JSON] = field(init=False)
    _done: bool = field(init=False)

    def __post_init__(self):
        self.idx = LSPClientRequest._gensym()
        self.result = None
        self._done = False

    GENSYM: ClassVar[int] = -1

    @staticmethod
    def _gensym():
        LSPClientRequest.GENSYM += 1
        return LSPClientRequest.GENSYM

    def json(self) -> JSON:
        return {**super().json(), "id": self.idx}

    def process_message(self, message: LSPServerMessage):
        super().process_message(message)
        if isinstance(message, LSPServerResponse) and message.idx == self.idx:
            self.result = message.result
            self._done = True
        elif isinstance(message, LSPServerError) and message.idx == self.idx:
            raise message.exn

    @property
    def done(self) -> bool:
        return self._done

@dataclass
class LSPServerRequest(LSPServerMessage):
    idx: int
    method: str
    params: dict[str, Any]

    @classmethod
    def from_json(cls, data: JSON) -> "Self":
        return cls(data["id"], data["method"], data.get("params", {}))

class LSPClientNotification(LSPClientQuery):
    @property
    def params(self) -> dict[str, Any]:
        return {}

    @property
    def done(self) -> bool:
        return True

@dataclass
class LSPServerNotification(LSPServerMessage):
    method: str
    params: dict[str, Any]

    @classmethod
    def from_json(cls, data: JSON) -> "Self":
        return cls(data["method"], data.get("params", {}))

class LSPServerNotifications:
    PUBLISH_DIAGNOSTICS = "textDocument/publishDiagnostics"
    SHOW_MESSAGE = "window/showMessage"
    LOG_MESSAGE = "window/logMessage"

@dataclass
class LSPServerResponse(LSPServerMessage):
    def __init__(self, idx: int, result: JSON):
        self.idx = idx
        self.result = result

    @classmethod
    def from_json(cls, data: JSON) -> "Self":
        return cls(data["id"], data.get("result", {}))

class LSPClientResponse(LSPClientMessage):
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

@dataclass
class LSPServerError(LSPServerMessage):
    idx: int
    code: int
    message: str

    @property
    def exn(self) -> LSPServerException:
        raise LSPServerException(self.message, self.code)

    @classmethod
    def from_json(cls, data: JSON) -> "Self":
        error_info = data["error"]
        return cls(data["id"], error_info["code"], error_info["message"])

@dataclass
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

@dataclass
class LSPServerConfig:
    capabilities: JSON
    driver_info: Optional[DriverInfo]

    @staticmethod
    def of_json(js: JSON) -> "LSPServerConfig":
        info, capabilities = js.get("serverInfo"), js["capabilities"]
        driver_info = DriverInfo(info["name"], info.get("version", "?")) if info else None
        return LSPServerConfig(capabilities, driver_info)

@dataclass
class LSPClientInitializeRequest(LSPClientRequest):
    METHOD = "initialize"

    CLIENT_NAME = "LSPClient"
    CAPABILITIES: ClassVar[JSON] = {
        "workspace": { "configuration": False },
        "textDocument": {
             "workspace": {
                 "configuration": False,
             },
             "textDocument": {
             }
         }
    }

    @property
    def params(self) -> JSON:
        return {
            "processId": __import__('os').getpid(),
            "clientInfo": {"name": self.CLIENT_NAME, "version": "1.0.0"},
            "rootUri": Path(os.getcwd()).as_uri(),
            "capabilities": self.CAPABILITIES
        }

    @property
    def config(self) -> LSPServerConfig:
        return LSPServerConfig.of_json(must(self.result))

class LSPInitializedNotification(LSPClientNotification):
    METHOD = "initialized"

@dataclass
class LSPClientDidOpenNotification(LSPClientNotification):
    METHOD = "textDocument/didOpen"

    uri: str
    text: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "languageId": self.client.LANGUAGE_ID,
                                   "version": 0, "text": self.text } }

class LSPClientShutdownRequest(LSPClientRequest):
    METHOD = "shutdown"

class LSPClientExitNotification(LSPClientNotification):
    METHOD = "exit"

@dataclass(frozen=True)
class LSPDiagnostic:
    SEVERITY_LEVELS: ClassVar[dict[int, int]] = { 1: 3, 2: 2, 3: 1, 4: 0, 5: 0 }

    fpath: str
    range: Range
    message: str
    severity: int

    @staticmethod
    def of_json(fpath: str, js: JSON):
        """Parse an LSP diagnostic."""
        return LSPDiagnostic(
            fpath, Range.of_lsp(fpath, js["range"]),
            js["message"], js.get("severity", 1)
        )

    def notify(self, obs: Observer, details: Optional[str]=""):
        level = self.SEVERITY_LEVELS[self.severity]
        obs.notify(None, self.message + (details or ""), self.range, level=level)

@dataclass(frozen=True)
class LSPMessage:
    message: str
    severity: int

    @staticmethod
    def of_json(js: JSON):
        return LSPMessage(js["message"], js["type"])

    def notify(self, obs: Observer):
        level = LSPDiagnostic.SEVERITY_LEVELS[self.severity]
        obs.notify(None, self.message, None, level=level)

TClientQuery = TypeVar("TClientQuery", bound=LSPClientQuery)

class LSPClient:
    LANGUAGE_ID: ClassVar[str]

    def __init__(self, driver: "LSPDriver[Self]"):
        self.driver: "LSPDriver[Self]" = driver
        self.config = self._init().send().config
        LSPInitializedNotification(self).send()

    @property
    def repl(self):
        return must(self.driver.repl)

    def receive_message(self) -> LSPServerMessage:
        assert self.repl.stdout
        return LSPServerMessage.from_stream(self.repl.stdout)

    def send_message(self, query: LSPClientMessage) -> None:
        bs = query.serialize()
        core_debug(bs, ">> ")
        self.repl.stdin.write(bs)
        self.repl.stdin.flush()

    def send_and_process(self, query: TClientQuery) -> TClientQuery:
        self.send_message(query)
        while not query.done:
            query.process_message(self.receive_message())
        return query

    def _init(self) -> LSPClientInitializeRequest:
        return LSPClientInitializeRequest(self)

    def kill(self):
        LSPClientShutdownRequest(self).send()
        LSPClientExitNotification(self).send()

TClient = TypeVar("TClient", bound=LSPClient, covariant=True)

class LSPFile(Generic[TClient]):
    def __init__(self, driver: "LSPDriver[TClient]", doc: Document):
        self.client = must(driver.client)
        self.observer = driver.observer
        self.fpath, self.uri = driver.fpath, driver.uri
        self.doc = doc
        self._open()

    def _open(self):
        LSPClientDidOpenNotification(self.client, self.uri, self.doc.str).send()

class LSPDocument(EncodedDocument):
    """Variant of ``Document`` in which positions are UTF-16 offsets, not char offsets."""
    ENCODING = "utf-16-le"

    @classmethod
    def _len(cls, s: str) -> int:
        return super()._len(s) // 2

    @overload
    @staticmethod
    def _map_index(i: slice) -> slice: ...
    @overload
    @staticmethod
    def _map_index(i: int) -> int: ...
    @overload
    @staticmethod
    def _map_index(i: None) -> None: ...

    @staticmethod
    def _map_index(i: int | slice | None) -> int | slice | None:
        if isinstance(i, slice):
            assert i.step in (1, None)
            return slice(LSPDocument._map_index(i.start),
                         LSPDocument._map_index(i.stop))
        return i * 2 if i is not None else None

    @classmethod
    def _slice(cls, s: str, index: slice) -> str:
        return super()._slice(s, cls._map_index(index))

    def __getitem__(self, index):
        return super().__getitem__(self._map_index(index))

    def __len__(self) -> int:
        return super().__len__() // 2

    def _find_bols(self) -> Iterable[int]:
        for pos in super()._find_bols():
            yield (pos + 1) // 2 # +1 because "\n" in UTF-16 is b"\n\x00"

    def _find_eol(self, start: int) -> int:
        return super()._find_eol(start * 2) // 2

class LSPDriver(PopenDriver, Generic[TClient]):
    STDIN_FILE_NAME: ClassVar[str]

    CLIENT: ClassVar[Type[TClient]] # type: ignore
    client: Optional[TClient] = None

    def version_info(self) -> DriverInfo:
        with self:
            return self.client.config.driver_info or DriverInfo(self.NAME, "?")

    def reset(self):
        super().reset()
        self.client = self.CLIENT(self)

    def kill(self):
        try:
            if self.client:
                self.client.kill()
        finally:
            self.client = None
            super().kill()

    @property
    def uri(self):
        fpath = Path(self.STDIN_FILE_NAME) if str(self.fpath) == "-" else self.fpath
        return fpath.absolute().as_uri()

    def _encode(self, chunks: Iterable[str]) -> Document:
        """Construct a document from `chunks`."""
        raise NotImplementedError

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        """Extract sentences (along with messages and goals) from `document`."""
        raise NotImplementedError

    def partition(self, document: Document):
        """Partition `document` into fragments."""
        return document.intersperse_text_fragments(self._find_sentences(document))

    def annotate(self, chunks: Iterable[str]) -> list[list[Fragment]]:
        r"""Annotate chunks of code.

        >>> from .vsrocq import VsRocq
        >>> VsRocq().annotate(["Check 1.", "Print False."])
        [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])],
         [Sentence(contents='Print False.', messages=[Message(contents='Inductive False : Prop :=  .')], goals=[])]]
        """
        document = self._encode(chunks)

        with self as api:
            try:
                fragments = api.partition(document)
                return list(document.recover_chunks(coalesce_text(fragments)))
            except LSPServerException as e:
                msg = f"LSP Server exception: {e}"
                api.observer.notify(None, msg, Position(api.fpath, 1, 0).as_range(), level=3)
                return [[Text(c)] for c in chunks]
