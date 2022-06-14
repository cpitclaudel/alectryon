# Copyright © 2019 Clément Pit-Claudel
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

from typing import Dict, Any, Optional, Tuple

import json
import pickle
import re
from copy import deepcopy
from functools import wraps
from importlib import import_module
from os import path, makedirs, unlink, fspath

from . import core, tokens

COMMENTS_RE = re.compile(r"^\s*//.*$", re.MULTILINE)
def uncomment(s):
    return COMMENTS_RE.sub("", s)

def loads(s, **kwargs):
    """Load a JSON document from string `s`, ignoring // comments."""
    return json.loads(uncomment(s), **kwargs)

TYPE_OF_ALIASES = {
    "text": core.Text,
    "hypothesis": core.Hypothesis,
    "goal": core.Goal,
    "message": core.Message,
    "sentence": core.Sentence,
    "goals": core.Goals,
    "messages": core.Messages,
    "tstr": tokens.TokenizedStr
}

ALIASES_OF_TYPE = {
    cls.__name__: alias for (alias, cls) in TYPE_OF_ALIASES.items()
}

TYPES = tuple(TYPE_OF_ALIASES.values())

class CacheState:
    def __init__(self, persistent: Optional[Dict[str, Dict[str, Any]]]=None):
        self.persistent: Dict[str, Dict[str, Any]] = persistent or {}
        self.ephemeral: Dict[str, Dict[str, Any]] = {}

    def specialize(self, key: str) -> Tuple[Dict[str, Any], Dict[str, Any]]:
        return (self.persistent.setdefault(key, {}),
                self.ephemeral.setdefault(key, {}))

class PlainSerializer:
    """Convert arrays and dictionaries of namedtuples to and from JSON.

    >>> from .core import Text as T
    >>> obj = {'a': [[1, T('A')], [1, T('A')], {'c': 3}], 'b': {'c': 3}}
    >>> enc = PlainSerializer.encode(obj, CacheState()); enc
    {'a': [[1, {'_type': 'text', 'contents': 'A'}],
           [1, {'_type': 'text', 'contents': 'A'}],
           {'c': 3}], 'b': {'c': 3}}
    >>> dec = PlainSerializer.decode(enc, CacheState()); dec
    {'a': [[1, Text(contents='A')], [1, Text(contents='A')], {'c': 3}], 'b': {'c': 3}}
    """
    @staticmethod
    def encode(obj: Any, memo: Optional[CacheState]=None) -> Any:
        memo = memo or CacheState()
        if isinstance(obj, list):
            return [PlainSerializer.encode(x, memo) for x in obj]
        if isinstance(obj, dict):
            assert "_type" not in obj
            return {k: PlainSerializer.encode(v, memo) for k, v in obj.items()}
        type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
        if type_name:
            d: Dict[str, Any] = {"_type": type_name} # Put _type first
            if hasattr(obj, "js_encode"):
                obj.js_encode(PlainSerializer, d, *memo.specialize(type_name))
            elif hasattr(obj, "_fields"):
                for k, v in zip(obj._fields, obj):
                    d[k] = PlainSerializer.encode(v, memo)
            return d
        assert obj is None or isinstance(obj, (int, str))
        return obj

    @staticmethod
    def decode(js, memo: Optional[CacheState]=None):
        memo = memo or CacheState()
        if isinstance(js, list):
            return [PlainSerializer.decode(x, memo) for x in js]
        if isinstance(js, dict):
            obj = {k: PlainSerializer.decode(v, memo) for k, v in js.items()}
            type_name = obj.pop("_type", None) # Avoid mutating `js`
            if type_name:
                typ = TYPE_OF_ALIASES[type_name]
                if hasattr(typ, "js_decode"):
                    return typ.js_decode(PlainSerializer, obj, # type: ignore
                                         *memo.specialize(type_name))
                return typ(**obj)
            return obj
        return js

class DeduplicatingSerializer:
    """Like `PlainSerializer`, but deduplicate references to objects in `TYPES`.
    Specifically, deduplication works by replacing repeated objects with a
    special dictionary ``{"*": N}``, where ``N`` is an index into the list of
    all objects encoded up to that point.

    >>> from .core import Text as T
    >>> obj = {'a': [[1, T('A')], [1, T('A')], {'c': 3}], 'b': {'c': 3}}
    >>> enc = DeduplicatingSerializer.encode(obj); enc
    {'a': [[1, {'&': 'text', '_': ['A']}], [1, {'*': 0}], {'c': 3}], 'b': {'c': 3}}
    >>> dec = DeduplicatingSerializer.decode(enc); dec
    {'a': [[1, Text(contents='A')], [1, Text(contents='A')], {'c': 3}], 'b': {'c': 3}}
    """
    @staticmethod
    def encode(obj):
        obj_table = {}
        def encode(obj):
            if isinstance(obj, list):
                return [encode(x) for x in obj]
            if isinstance(obj, dict):
                assert "*" not in obj and "&" not in obj
                return {k: encode(v) for k, v in sorted(obj.items())}
            type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
            if type_name:
                key = pickle.dumps(obj)
                if key in obj_table:
                    return {"*": obj_table[key]}
                d = {"&": type_name, "_": [encode(v) for v in obj]}
                obj_table[key] = len(obj_table)
                return d
            assert obj is None or isinstance(obj, (int, str))
            return obj
        return encode(obj)

    @staticmethod
    def decode(js, copy=False):
        obj_table = []
        def decode(js):
            if isinstance(js, list):
                return [decode(x) for x in js]
            if isinstance(js, dict):
                if "*" in js: # Pointer
                    obj = obj_table[js["*"]]
                    return deepcopy(obj) if copy else obj
                if "&" in js: # Reference
                    obj = TYPE_OF_ALIASES[js["&"]](*(decode(v) for v in js["_"]))
                    obj_table.append(obj)
                    return obj
                return {k: decode(v) for k, v in sorted(js.items())}
            return js
        return decode(js)

class FullyDeduplicatingSerializer:
    """Like `DeduplicatingSerializer`, but also deduplicate basic types.

    >>> from .core import Text as T
    >>> obj = {'a': [[1, T('A')], [1, T('A')], {'c': 3}], 'b': {'c': 3}}
    >>> enc = FullyDeduplicatingSerializer.encode(obj); enc
    {'a': [[1, {'&': 'text', '_': ['A']}], {'*': 3}, {'c': 3}], 'b': {'*': 5}}
    >>> dec = FullyDeduplicatingSerializer.decode(enc); dec
    {'a': [[1, Text(contents='A')], [1, Text(contents='A')], {'c': 3}], 'b': {'c': 3}}
    """
    @staticmethod
    def encode(obj):
        obj_table = {}
        def encode(obj):
            key = pickle.dumps(obj)
            ref = obj_table.get(key)
            if ref is not None:
                return {"*": ref}
            val = _encode(obj)
            obj_table[key] = len(obj_table)
            return val
        def _encode(obj):
            if isinstance(obj, list):
                return [encode(x) for x in obj]
            if isinstance(obj, dict):
                assert "*" not in obj and "&" not in obj
                return {k: encode(v) for k, v in sorted(obj.items())}
            type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
            if type_name:
                return {"&": type_name, "_": [encode(v) for v in obj]}
            assert obj is None or isinstance(obj, (int, str))
            return obj
        return encode(obj)

    @staticmethod
    def decode(js, copy=False):
        obj_table = []
        def decode(js):
            if isinstance(js, dict) and "*" in js:
                obj = obj_table[js["*"]]
                return deepcopy(obj) if copy else obj
            obj = _decode(js)
            obj_table.append(obj)
            return obj
        def _decode(js):
            if isinstance(js, list):
                return [decode(x) for x in js]
            if isinstance(js, dict):
                if "&" in js:
                    return TYPE_OF_ALIASES[js["&"]](*(decode(v) for v in js["_"]))
                return {k: decode(v) for k, v in sorted(js.items())}
            return js
        return decode(js)

def deprecated(old_name):
    def _wrap(fn):
        @wraps(fn)
        def _fn(*args, **kwargs):
            import warnings
            MSG = "Function {} deprecated; use {} instead."
            warnings.warn(MSG.format(old_name, fn.__name__),
                          category=DeprecationWarning, stacklevel=2)
            return fn(*args, **kwargs)
        return _fn
    return _wrap

@deprecated
def json_of_annotated(obj):
    return PlainSerializer.encode(obj, CacheState())
@deprecated
def annotated_of_json(obj):
    return PlainSerializer.decode(obj, CacheState())

def validate_metadata(metadata, reference, cache_file):
    if metadata != reference:
        MSG = "Outdated metadata in {} ({} != {})"
        print(MSG.format(cache_file, metadata, reference))
        return False
    return True

def validate_data(data, reference, cache_file):
    if data != reference:
        MSG = "Outdated contents in {}: recomputing"
        print(MSG.format(cache_file))
        return False
    return True

class Cache:
    def __init__(self, data, cache_file):
        self.data = data
        self.cache_file = cache_file
        self.serializer = PlainSerializer

    @staticmethod
    def normalize(obj: Any) -> Any:
        if isinstance(obj, (list, tuple)):
            return [Cache.normalize(o) for o in obj]
        if isinstance(obj, dict):
            return {k: Cache.normalize(v) for (k, v) in obj.items()}
        return obj

    def _validate(self, chunks, metadata):
        # Note that we validate "metadata" but not "driver".  This is to prevent
        # Coq upgrades from invalidating caches.  It's easy to force invalidation
        # by hand (delete the caches), whereas automatic invalidation on Coq
        # upgrades would make it a pain to keep a collection of examples (say, a
        # blog) with dependencies on different libraries and Coq versions.
        return (self.data is not None
           and validate_metadata(self.data["metadata"], metadata, self.cache_file)
           and validate_data(self.data.get("chunks"), chunks, self.cache_file))

    def get(self, chunks, metadata):
        if not self._validate(self.normalize(chunks), self.normalize(metadata)):
            return None
        return self.serializer.decode(self.data.get("annotated"),
                                      CacheState(self.data.get("memo", {})))

    @property
    def driver_info(self):
        return core.DriverInfo(*self.data.get("driver", ("Coq+SerAPI", "??")))

    def put(self, chunks, metadata, annotated, driver):
        memo = CacheState()
        self.data = {"driver": self.normalize(driver),
                     "metadata": self.normalize(metadata),
                     "chunks": list(chunks),
                     "annotated": self.serializer.encode(annotated, memo),
                     "memo": memo.persistent}

    def update(self, chunks, driver):
        annotated = self.get(chunks, driver.metadata)
        if annotated is None:
            annotated = driver.annotate(chunks)
            self.put(chunks, driver.metadata, annotated, driver.version_info())
        return annotated

class BaseCacheSet:
    def __enter__(self):
        raise NotImplementedError()
    def __exit__(self, *_exn):
        raise NotImplementedError()
    def __getitem__(self, lang):
        raise NotImplementedError()

class TrivialCacheSet(BaseCacheSet):
    def __init__(self, *_args):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *_exn):
        return False

    def __getitem__(self, lang):
        return Cache(None, None)

class FileCacheSet(BaseCacheSet):
    CACHE_VERSION = "2"

    LANG_PREFIX = "&"
    METADATA = {"cache_version": CACHE_VERSION}

    KNOWN_COMPRESSIONS = {
        "none": ("builtins", ""),
        "gzip": ("gzip", ".gz"),
        "xz": ("lzma", ".xz"),
    }

    def __init__(self, cache_root: str, doc_path: str, cache_compression):
        self.cache_root = path.realpath(fspath(cache_root))
        self.wanted_compression = cache_compression or "none"
        if self.wanted_compression not in self.KNOWN_COMPRESSIONS:
            raise ValueError("Unsupported cache compression: {}".format(cache_compression))

        doc_path = path.realpath(fspath(doc_path))
        doc_root = path.commonpath((self.cache_root, doc_path))
        self.cache_rel_file = path.relpath(doc_path, doc_root) + ".cache"
        self.cache_file = path.join(cache_root, self.cache_rel_file)
        self.cache_dir = path.dirname(self.cache_file)
        makedirs(self.cache_dir, exist_ok=True)

        self.ondisk_compression, self.js = self._read()
        self.caches = self._read_caches() if self._validate() else {}

    def __enter__(self):
        return self

    def __exit__(self, *_exn):
        self._write()
        return False

    @classmethod
    def _upgrade(cls, contents):
        """Upgrade old cache contents to the latest cache version.

        (Breaking compatibility with old caches is undesirable, because such
        caches may have been created with old versions of Coq or old source code
        and may not be easy to rebuild, so we prefer to have an upgrade path).
        """
        metadata = contents.get("metadata", {})
        version = metadata.get("cache_version")
        if version == "1":
            metadata.pop("cache_version", None)
            return {"metadata": cls.METADATA,
                    **{cls.LANG_PREFIX + "coq":
                       {"driver": contents.pop("generator"),
                        "metadata": contents.pop("metadata"),
                        **contents}}}
        return contents

    def _read_caches(self):
        assert self.js is not None
        return {key[len(self.LANG_PREFIX):]: Cache(data, self.cache_rel_file)
                for key, data in sorted(self.js.items())
                if key.startswith(self.LANG_PREFIX)}

    def _open(self, compression, mode):
        mod, ext = self.KNOWN_COMPRESSIONS[compression]
        return import_module(mod).open(self.cache_file + ext, mode=mode) # type: ignore

    def _read(self):
        for compression in self.KNOWN_COMPRESSIONS:
            try:
                with self._open(compression, mode="rt") as cache:
                    return compression, self._upgrade(loads(cache.read()))
            except FileNotFoundError:
                pass
        return None, None

    def _validate(self):
        return self.js and validate_metadata(self.js["metadata"], self.METADATA,
                                           self.cache_rel_file)

    def __getitem__(self, lang):
        if lang not in self.caches:
            self.caches[lang] = Cache(None, self.cache_rel_file)
        return self.caches[lang]

    def _check_recompression(self):
        needed = self.ondisk_compression != self.wanted_compression
        if needed:
            MSG = "Recompression requested for {} " \
                "(was {}, now {}): rewriting cache file"
            print(MSG.format(self.cache_rel_file,
                             self.ondisk_compression,
                             self.wanted_compression))
        return needed

    def _delete_old_caches(self):
        for _mod, ext in self.KNOWN_COMPRESSIONS.values():
            try:
                unlink(self.cache_file + ext)
            except FileNotFoundError:
                pass

    def _force_write(self, js):
        self._delete_old_caches()
        with self._open(self.wanted_compression, mode="wt") as cache:
            json.dump(js, cache, indent=2)
        self.js, self.ondisk_compression = js, self.wanted_compression

    def _write(self):
        js = { "metadata": self.METADATA,
               **{ self.LANG_PREFIX + lang: c.data
                   for (lang, c) in sorted(self.caches.items()) } }
        if js != self.js or self._check_recompression():
            self._force_write(js)

def CacheSet(cache_root, doc_path, cache_compression) -> BaseCacheSet:
    cls = FileCacheSet if cache_root is not None else TrivialCacheSet
    return cls(cache_root, doc_path, cache_compression)
