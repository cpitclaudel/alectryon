from typing import Any, Callable, Dict, List, NamedTuple, Optional, Union
from enum import Enum
import json
import os
import re
from pathlib import Path
from subprocess import Popen

from .core import debug as core_debug

JSON = Dict[str, Any]

class LSPException(Exception):
    """Exception raised for LSP errors"""
    def __init__(self, message: str, code: int = -1):
        super().__init__(message)
        self.code = code

    @classmethod
    def from_json(cls, data: Dict[str, Any]) -> 'LSPException':
        """Create LSPException from JSON error data"""
        error_info = data["error"]
        return cls(error_info.get("message", "Unknown error"), 
                  error_info.get("code", -1))

class LSPMethod:
    @property
    def value(self) -> str:
        return getattr(self, "_value_", str(self))

class LSPRequestList(LSPMethod, Enum):
    INITIALIZE = "initialize"
    SHUTDOWN = "shutdown"
    SEMANTIC_TOKENS_FULL = "textDocument/semanticTokens/full"

class LSPNotificationList(LSPMethod, Enum):
    INITIALIZED = "initialized"
    DID_OPEN = "textDocument/didOpen" 
    EXIT = "exit"
    PUBLISH_DIAGNOSTICS = "textDocument/publishDiagnostics"

class LSPErrorCode:
    PARSING_NOT_FINISHED = -32802
    METHOD_NOT_FOUND = -32601

class LSPMessage:
    """Base class for all LSP messages"""
    @classmethod
    def from_json(cls, data: Dict) -> 'LSPMessage':
        idx = data.get("id")
        method = data.get("method")
        
        if method is not None:
            if idx is not None:
                return LSPRequest.from_json(data)
            else:
                return LSPNotification.from_json(data)
        else:
            if "error" in data:
                raise LSPException.from_json(data)
            else:
                return LSPResponse.from_json(data)
    
    def json(self) -> JSON:
        raise NotImplementedError()

class LSPQuery(LSPMessage):
    """Base class for LSP Requests and notifications"""

    def process_incoming(self, incoming: 'LSPMessage') -> bool:
        raise NotImplementedError()
    
    def handle_notification(self, notification: 'LSPNotification') -> None:
        """Handles incoming notifications"""
        if not hasattr(self, 'collected_notifications'):
            self.collected_notifications = []
        self.collected_notifications.append(notification)
    
    @property
    def is_done(self) -> bool:
        """Checks if this message is complete"""
        raise NotImplementedError()
    
class LSPRequest(LSPQuery):
    """LSP Request that expects a response"""

    def __init__(self, idx: int, method: Union[LSPMethod, str], params: Optional[JSON] = None):
        self.idx = idx
        self.method = method
        self.params = params or {}
        self.result: Optional[JSON] = None
        self.collected_notifications: List['LSPNotification'] = []

    @classmethod
    def from_json(cls, data: Dict) -> 'LSPRequest':
        return cls(data["id"], data["method"], data.get("params", {}))

    def json(self) -> JSON:
        method_str = getattr(self.method, "value", str(self.method))
        return {
            "jsonrpc": "2.0",
            "id": self.idx,
            "method": method_str,
            "params": self.params
        }
    
    def process_incoming(self, incoming: 'LSPMessage') -> bool:
        if isinstance(incoming, LSPResponse) and incoming.idx == self.idx:
            self.result = incoming.result
            return True
        elif isinstance(incoming, LSPNotification):
            self.handle_notification(incoming)
            return False
        elif isinstance(incoming, LSPError) and incoming.idx == self.idx:
            raise LSPException(incoming.message, incoming.code)
        else:
            return False

    @property
    def is_done(self) -> bool:
        return self.result is not None
    
class LSPNotification(LSPQuery):
    """LSP Notification (no response expected)"""

    def __init__(self, method: Union[LSPMethod, str], params = None):
        self.method = method
        self.params = params or {}
        self.collected_notifications: List['LSPNotification'] = []

    @classmethod
    def from_json(cls, data: Dict) -> 'LSPNotification':
        """Create LSPNotification from JSON data"""
        return cls(data["method"], data.get("params", {}))

    def json(self) -> JSON:
        """Convert notification to JSON for sending"""
        method_str = getattr(self.method, "value", str(self.method))
        return {
            "jsonrpc": "2.0",
            "method": method_str,
            "params": self.params
        }
    
    def process_incoming(self, incoming: 'LSPMessage') -> bool:
        if isinstance(incoming, LSPNotification):
            self.handle_notification(incoming)
            return self.is_done
        return False
    
    @property
    def is_done(self) -> bool:
        return True

class LSPResponse(LSPMessage):
    """LSP Response to a request"""
    
    def __init__(self, idx: int, result: JSON):
        self.idx = idx
        self.result = result

    @classmethod
    def from_json(cls, data: Dict) -> 'LSPResponse':
        """Create LSPResponse from JSON data"""
        return cls(data["id"], data.get("result", {}))
    
    def json(self) -> JSON:
        """Convert response to JSON for sending"""
        return {
            "jsonrpc": "2.0", 
            "id": self.idx, 
            "result": self.result
        }
    
class LSPError(LSPMessage):
    """LSP Error response"""

    def __init__(self, idx: int, code: int, message: str):
        self.idx = idx
        self.code = code
        self.message = message

    @classmethod
    def from_json(cls, data: Dict) -> 'LSPError':
        """Create LSPError from JSON data"""
        error_info = data["error"]
        return cls(data["id"], error_info["code"], error_info["message"])

    def json(self) -> JSON:
        """Convert error to JSON for sending"""
        return {
            "jsonrpc": "2.0", 
            "id": self.idx,
            "error": {"code": self.code, "message": self.message}
        }

class LSPParser:
    """Parser for LSP messages"""
    JRPC_HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    @staticmethod
    def serialize(query: LSPMessage) -> bytes:
        js = json.dumps(query.json(), indent=1).replace("\n", "\r\n") + "\r\n"
        header = f"Content-Length: {len(js)}\r\n\r\n"
        return header.encode("utf-8") + js.encode("utf-8")

    @staticmethod
    def from_stream(stream) -> LSPMessage:
        """Read and parse an LSP message from stream"""
        line, length = None, None
        while line not in ("", "\r\n"):
            line = stream.readline().decode("utf-8")
            core_debug(repr(line), "<< ")
            header = LSPParser.JRPC_HEADER_RE.match(line)
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
        
        return LSPMessage.from_json(data)

class LSPClient:    
    CLIENT_NAME = "Alectryon"
    LANGUAGE_ID = "coq"

    def __init__(self, repl: Popen, debug_func=None):
        self.repl = repl
        self.debug_func = debug_func or core_debug
        self.parser = LSPParser()
        self.root_uri = Path(os.getcwd()).as_uri()
        self.next_request_id = 1
        self.initialized = False

    INITIAL_PARSING_DELAY = 0.05
    PARSING_DELAY_MULTIPLIER = 2.0

    CAPABILITIES = {
        "workspace": { "configuration": False },
        "textDocument": {}
    }
    
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

    def initialize(self) -> bool:
        try:
            init_query = LSPRequest(
                self.get_next_request_id(), LSPRequestList.INITIALIZE, {
                    "processId": __import__('os').getpid(),
                    "clientInfo": {"name": self.CLIENT_NAME, "version": "1.0.0"},
                    "rootUri": self.root_uri,
                    "capabilities": self.CAPABILITIES
                }
            )
            self.send_and_process(init_query)
            return True
        except LSPException:
            return False
        
    def send_initialized(self) -> None:
        initialized = LSPNotification(LSPNotificationList.INITIALIZED, {})
        self.send_and_process(initialized)
        self.initialized = True

    def open_document(self, uri: str, contents: str) -> None:
        open_doc = LSPNotification(LSPNotificationList.DID_OPEN, {
            "textDocument": {"uri": uri, "languageId": "coq", "version": 0, "text": contents}
        })
        self.send_message(open_doc)

    def shutdown(self) -> None:
        if not self.initialized:
            return
        
        try:
            shutdown_query = LSPRequest(self.get_next_request_id(), LSPRequestList.SHUTDOWN, {})
            self.send_and_process(shutdown_query)
        except LSPException as e:
            print(f"Shutdown failed: {e}")

    def exit(self) -> None:
        self.send_message(LSPNotification(LSPNotificationList.EXIT, {}))
        self.initialized = False
    
    def debug(self, message, prefix=""):
        if self.debug_func:
            self.debug_func(message, prefix)
    
    def get_next_request_id(self) -> int:
        request_id = self.next_request_id
        self.next_request_id += 1
        return request_id
    
    def send_message(self, query: LSPMessage) -> None:
        bs = self.parser.serialize(query)
        self.debug(bs, ">> ")
        self.repl.stdin.write(bs)
        self.repl.stdin.flush()
    
    def receive_message(self) -> LSPMessage:
        return self.parser.from_stream(self.repl.stdout)

    def send_and_process(self, query: LSPQuery) -> LSPQuery:
        self.send_message(query)

        if query.is_done:
            return query
        
        while True:
            try:
                incoming = self.receive_message()

                if isinstance(incoming, LSPRequest):
                    error_response = LSPError(
                        incoming.idx, LSPErrorCode.METHOD_NOT_FOUND, 
                        "This client does not support server requests."
                    )
                    self.send_message(error_response)
                    continue

                is_complete = query.process_incoming(incoming)
                if is_complete:
                    break
            except LSPException as e:
                raise e
            
        return query