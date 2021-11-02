# TODO: Add license

import tempfile
import os
from pathlib import Path
from .core import CLIDriver, EncodedDocument, Positioned, Sentence

class Lean4(CLIDriver):
    BIN = "leanInk"
    NAME = "Lean4"

    VERSION_ARGS = ("lV",)

    ID = "leanInk"
    LANGUAGE = "lean4"

    CLI_ARGS = ("analyze",)

    TMP_PREFIX = "leanInk_"

    def run_leanInk(self, encoded_document):
        with tempfile.TemporaryDirectory(prefix=self.TMP_PREFIX) as working_directory:
            source = Path(working_directory) / os.path.basename(self.fpath)
            source.write_bytes(encoded_document.contents)
            result = self.run_cli(more_args=[str(source)])

            print(result)

    def annotate(self, chunks):
        print("Hello from Lean4 driver")
        self.run_leanInk(EncodedDocument(chunks, "\n", encoding="utf-8")) # Actually use the info from LeanInk to annotate chunks
        return [] # TODO: Actually return something usefull