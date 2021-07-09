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
from os import path, makedirs
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

def compact_json_of_annotated(obj):
    import pickle # use pickle to memoize unhashable types
    obj_table = {}
    def encode(obj):
        if isinstance(obj, list):
            return [encode(x) for x in obj]
        if isinstance(obj, dict):
            assert "_type" not in obj
            return {k: encode(v) for k, v in sorted(obj.items())}
        type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
        if type_name:
            key = pickle.dumps(obj)
            ref = obj_table.get(key)
            if ref is not None:
                return {"&": ref}
            d = {k: encode(v) for k, v in sorted(obj._asdict().items())}
            d["_type"] = type_name
            obj_table[key] = len(obj_table)
            return d
        assert obj is None or isinstance(obj, (int, str))
        return obj
    return encode(obj)

from copy import deepcopy

def annotated_of_compact_json(js, copy=False):
    obj_table = []
    def decode(js):
        if isinstance(js, list):
            return [decode(x) for x in js]
        if isinstance(js, dict):
            ref = js.get("&")
            if ref is not None:
                obj = obj_table[ref]
                return deepcopy(obj) if copy else obj
            type_name = js.pop("_type", None)
            obj = {k: decode(v) for k, v in sorted(js.items())}
            if type_name:
                obj = TYPE_OF_ALIASES[type_name](**obj)
                obj_table.append(obj)
            return obj
        return js
    return decode(js)

def deep_compact_json_of_annotated(obj):
    import pickle
    obj_table = {}
    def encode(obj):
        key = pickle.dumps(obj)
        ref = obj_table.get(key)
        if ref is not None:
            return {"&": ref}
        val = _encode(obj)
        obj_table[key] = len(obj_table)
        return val
    def _encode(obj):
        if isinstance(obj, list):
            return [encode(x) for x in obj]
        if isinstance(obj, dict):
            return {k: encode(v) for k, v in sorted(obj.items())}
        type_name = ALIASES_OF_TYPE.get(type(obj).__name__)
        if type_name:
            d = {k: encode(v) for k, v in sorted(obj._asdict().items())}
            d["_type"] = type_name
            return d
        assert obj is None or isinstance(obj, (int, str))
        return obj
    return encode(obj)

def annotated_of_deep_compact_json(js, copy=False):
    obj_table = []
    def decode(js):
        ref = js.get("&") if isinstance(js, dict) else None
        if ref is not None:
            obj = obj_table[ref]
            return deepcopy(obj) if copy else obj
        obj = _decode(js)
        obj_table.append(obj)
        if obj == "sentence":
            breakpoint()
        return obj
    def _decode(js):
        if isinstance(js, list):
            return [decode(x) for x in js]
        if isinstance(js, dict):
            type_name = js.pop("_type", None)
            obj = {k: decode(v) for k, v in sorted(js.items())}
            if type_name:
                obj = TYPE_OF_ALIASES[type_name](**obj)
            return obj
        return js
    return decode(js)

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

class BaseCache:
    def get(self, chunks):
        raise NotImplementedError

    def put(self, chunks, annotated, generator):
        raise NotImplementedError

    # LATER: pass a SerAPI instance instead of update_fn and generator
    def update(self, chunks, update_fn, generator):
        annotated = self.get(chunks)
        if annotated is None:
            annotated = update_fn(chunks)
            self.put(chunks, annotated, generator)
        return annotated

class FileCache(BaseCache):
    CACHE_VERSION = "1"

    def __init__(self, cache_root, doc_path, metadata):
        self.serializer = PlainSerializer
        self.cache_root = path.realpath(cache_root)
        doc_root = path.commonpath((self.cache_root, path.realpath(doc_path)))
        self.cache_rel_file = path.relpath(doc_path, doc_root) + ".cache"
        self.cache_file = path.join(cache_root, self.cache_rel_file)
        self.cache_dir = path.dirname(self.cache_file)
        makedirs(self.cache_dir, exist_ok=True)
        self.metadata = self.normalize(metadata)
        self.metadata["cache_version"] = self.CACHE_VERSION
        self.data = self._read()

    @staticmethod
    def normalize(obj):
        if isinstance(obj, (list, tuple)):
            return [FileCache.normalize(o) for o in obj]
        if isinstance(obj, dict):
            return {k: FileCache.normalize(v) for (k, v) in obj.items()}
        return obj

    def _validate(self, data, reference):
        metadata = data.get("metadata")
        if self.metadata != metadata:
            MSG = "Outdated metadata in {} ({} != {}): recomputing annotations"
            print(MSG.format(self.cache_rel_file, self.metadata, metadata))
            return False
        reference = self.normalize(reference)
        if reference != data.get("chunks"):
            MSG = "Outdated contents in {}: recomputing"
            print(MSG.format(self.cache_rel_file))
            return False
        return True

    def _read(self):
        try:
            with open(self.cache_file) as cache:
                return self.normalize(json.load(cache))
        except FileNotFoundError:
            return None

    def get(self, chunks):
        if self.data is None or not self._validate(self.data, chunks):
            return None
        return self.serializer.decode(self.data.get("annotated"))

    @property
    def generator(self):
        return core.GeneratorInfo(*self.data.get("generator", ("Coq+SerAPI", "??")))

    def put(self, chunks, annotated, generator):
        with open(self.cache_file, mode="w") as cache:
            self.data = {"generator": generator,
                         "metadata": self.metadata,
                         "chunks": list(chunks),
                         "annotated": self.serializer.encode(annotated)}
            json.dump(self.data, cache, indent=2)

class DummyCache(BaseCache):
    def __init__(self, *_args):
        self.generator = None

    def get(self, *_args): # pylint: disable=no-self-use
        return None

    def put(self, _chunks, _annotated, generator):
        self.generator = generator

def Cache(cache_root, doc_path, sertop_args):
    metadata = {"sertop_args": sertop_args}
    cls = FileCache if cache_root is not None else DummyCache
    return cls(cache_root, doc_path, metadata)
