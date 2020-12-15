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

import json
import pickle
from copy import deepcopy
from os import path, makedirs, unlink
from itertools import zip_longest

from . import core

TYPE_OF_ALIASES = {
    "text": core.Text,
    "hypothesis": core.Hypothesis,
    "goal": core.Goal,
    "message": core.Message,
    "sentence": core.Sentence,
    "goals": core.Goals,
    "messages": core.Messages,
    "rich_sentence": core.RichSentence,
}

ALIASES_OF_TYPE = {
    cls.__name__: alias for (alias, cls) in TYPE_OF_ALIASES.items()
}

TYPES = list(TYPE_OF_ALIASES.values())

class PlainSerializer:
    @staticmethod
    def encode(obj):
        if isinstance(obj, list):
            return [PlainSerializer.encode(x) for x in obj]
        if isinstance(obj, dict):
            assert "_type" not in obj
            return {k: PlainSerializer.encode(v) for k, v in obj.items()}
        type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
        if type_name:
            d = {"_type": type_name} # Put _type first
            for k, v in zip(obj._fields, obj):
                d[k] = PlainSerializer.encode(v)
            return d
        assert obj is None or isinstance(obj, (int, str))
        return obj

    @staticmethod
    def decode(js):
        if isinstance(js, list):
            return [PlainSerializer.decode(x) for x in js]
        if isinstance(js, dict):
            obj = {k: PlainSerializer.decode(v) for k, v in js.items()}
            type_name = obj.pop("_type", None) # Avoid mutating `js`
            if type_name:
                return TYPE_OF_ALIASES[type_name](**obj)
            return obj
        return js

class DeduplicatingSerializer:
    """Like `PlainSerializer`, but deduplicate references to objects in `TYPES`.
    Specifically, deduplication works by replacing repeated objects with a
    special dictionary ``{"&": N}``, where ``N`` is an index into the list of
    all objects encoded up to that point.
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
    """Like `DeduplicatingSerializer`, but also deduplicate basic types."""
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

from functools import wraps

def deprecated(fn, old_name):
    @wraps(fn)
    def _fn(*args, **kwargs):
        import warnings
        MSG = "Function {} deprecated; use {} instead."
        warnings.warn(MSG.format(old_name, fn.__name__),
                      category=DeprecationWarning, stacklevel=2)
        return fn(*args, **kwargs)
    return _fn

json_of_annotated = deprecated(PlainSerializer.encode, "json_of_annotated")
annotated_of_json = deprecated(PlainSerializer.decode, "annotated_of_json")

def validate_inputs(annotated, reference):
    if isinstance(annotated, list):
        if not isinstance(reference, list):
            print(f"Mismatch: {annotated} {reference}")
            return False
        return all(validate_inputs(*p) for p in zip_longest(annotated, reference))
    # pylint: disable=isinstance-second-argument-not-valid-type
    if isinstance(annotated, TYPES):
        if annotated.contents != reference:
            print(f"Mismatch: {annotated.contents} {reference}")
        return annotated.contents == reference
    return False

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
    def normalize(obj):
        if isinstance(obj, (list, tuple)):
            return [Cache.normalize(o) for o in obj]
        if isinstance(obj, dict):
            return {k: Cache.normalize(v) for (k, v) in obj.items()}
        return obj

    def _validate(self, chunks, metadata):
        return (self.data is not None
           and validate_metadata(self.data["metadata"], metadata, self.cache_file)
           and validate_data(self.data.get("chunks"), chunks, self.cache_file))

    def get(self, chunks, metadata):
        if not self._validate(self.normalize(chunks), self.normalize(metadata)):
            return None
        return self.serializer.decode(self.data.get("annotated"))

    @property
    def generator(self):
        return core.GeneratorInfo(*self.data.get("generator", ("Coq+SerAPI", "??")))

    def put(self, chunks, metadata, annotated, generator):
        self.data = {"generator": self.normalize(generator),
                     "metadata": self.normalize(metadata),
                     "chunks": list(chunks),
                     "annotated": self.serializer.encode(annotated)}

    # FIXME: pass a prover instance instead of update_fn and generator
    def update(self, chunks, metadata, update_fn, generator):
        annotated = self.get(chunks, metadata)
        if annotated is None:
            annotated = update_fn(chunks)
            self.put(chunks, metadata, annotated, generator)
        return annotated

class FileCacheSet:
    CACHE_VERSION = "2"
    METADATA = {"cache_version": CACHE_VERSION}

    KNOWN_COMPRESSIONS = {
        "none": ("builtins", ""),
        "gzip": ("gzip", ".gz"),
        "xz": ("lzma", ".xz"),
    }

    def __init__(self, cache_root, doc_path, cache_compression):
        self.cache_root = path.realpath(cache_root)
        self.wanted_compression = cache_compression or "none"
        if self.wanted_compression not in self.KNOWN_COMPRESSIONS:
            raise ValueError("Unsupported cache compression: {}".format(cache_compression))

        doc_root = path.commonpath((self.cache_root, path.realpath(doc_path)))
        self.cache_rel_file = path.relpath(doc_path, doc_root) + ".cache"
        self.cache_file = path.join(cache_root, self.cache_rel_file)
        self.cache_dir = path.dirname(self.cache_file)
        makedirs(self.cache_dir, exist_ok=True)

        self.ondisk_compression, self.js = self._read()
        self.caches = {}
        if self._validate():
            for lang, data in sorted(self.js["caches"].items()):
                self.caches[lang] = Cache(data, self.cache_rel_file)

    def __enter__(self):
        return self

    def __exit__(self, *_exn):
        self._write()
        return False

    def _open(self, compression, mode):
        mod, ext = self.KNOWN_COMPRESSIONS[compression]
        return __import__(mod).open(self.cache_file + ext, mode=mode)

    def _read(self):
        for compression in self.KNOWN_COMPRESSIONS:
            try:
                with self._open(compression, mode="rt") as cache:
                    return compression, json.load(cache)
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
               "caches": { lang: c.data
                           for (lang, c) in sorted(self.caches.items()) } }
        if js != self.js or self._check_recompression():
            self._force_write(js)

class DummyCacheSet():
    def __init__(self, *_args):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *_exn):
        return False

    def __getitem__(self, lang):
        return Cache(None, None)

def CacheSet(cache_root, doc_path, cache_compression):
    cls = FileCacheSet if cache_root is not None else DummyCacheSet
    return cls(cache_root, doc_path, cache_compression)
