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

from .core import CoqHypothesis, CoqGoal, CoqSentence, HTMLSentence, CoqText

COQ_TYPE_OF_ALIASES = {
    "hypothesis": CoqHypothesis,
    "goal": CoqGoal,
    "sentence": CoqSentence,
    "html_sentence": HTMLSentence,
    "text": CoqText,
}

ALIASES_OF_COQ_TYPE = {
    cls.__name__: alias for (alias, cls) in COQ_TYPE_OF_ALIASES.items()
}

COQ_TYPES = list(COQ_TYPE_OF_ALIASES.values())

def json_of_annotated(obj):
    if isinstance(obj, list):
        return [json_of_annotated(x) for x in obj]
    if isinstance(obj, dict):
        return {k: json_of_annotated(v) for k, v in obj.items()}
    type_name = ALIASES_OF_COQ_TYPE.get(type(obj).__name__)
    if type_name:
        d = {k: json_of_annotated(v) for k, v in zip(obj._fields, obj)}
        return {"_type": type_name, **d}
    return obj

def annotated_of_json(js):
    if isinstance(js, list):
        return [annotated_of_json(x) for x in js]
    if isinstance(js, dict):
        type_name = js.get("_type")
        type_constr = COQ_TYPE_OF_ALIASES.get(type_name)
        coq = {k: annotated_of_json(v) for k, v in js.items()}
        if type_constr:
            del coq["_type"]
            return type_constr(**coq)
        return coq
    return js

def validate_inputs(annotated, reference):
    if isinstance(annotated, list):
        if not isinstance(reference, list):
            print(f"Mismatch: {annotated} {reference}")
            return False
        return all(validate_inputs(*p) for p in zip_longest(annotated, reference))
    if isinstance(annotated, COQ_TYPES):
        if annotated.contents != reference:
            print(f"Mismatch: {annotated.contents} {reference}")
        return annotated.contents == reference
    return False


class FileCache:
    def __init__(self, cache_root, doc_path, metadata):
        self.cache_root = path.realpath(cache_root)
        doc_root = path.commonpath((self.cache_root, path.realpath(doc_path)))
        self.cache_rel_file = path.relpath(doc_path, doc_root) + ".cache"
        self.cache_file = path.join(cache_root, self.cache_rel_file)
        self.cache_dir = path.dirname(self.cache_file)
        makedirs(self.cache_dir, exist_ok=True)
        self.metadata = self.normalize(metadata)

    @staticmethod
    def normalize(obj):
        if isinstance(obj, (list, tuple)):
            return [FileCache.normalize(o) for o in obj]
        if isinstance(obj, dict):
            return {k: FileCache.normalize(v) for (k, v) in obj.items()}
        return obj

    def validate(self, data, reference):
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

    def get(self, chunks):
        try:
            with open(self.cache_file) as cache:
                data = self.normalize(json.load(cache))
        except FileNotFoundError:
            return None
        if not self.validate(data, chunks):
            return None
        return annotated_of_json(data.get("annotated"))

    def put(self, chunks, annotated):
        with open(self.cache_file, mode="w") as cache:
            data = { "metadata": self.metadata,
                     "chunks": list(chunks),
                     "annotated": json_of_annotated(annotated) }
            json.dump(data, cache, indent=2)

class DummyCache:
    def __init__(self, *_args):
        pass

    def get(self, *_args):
        return None

    def put(self, *_args):
        pass

def Cache(cache_root, doc_path, sertop_args):
    metadata = { "sertop_args": sertop_args }
    cls = FileCache if cache_root is not None else DummyCache
    return cls(cache_root, doc_path, metadata)
