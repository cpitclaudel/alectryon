# TODO: Add license

import tempfile
import os
from pathlib import Path
from alectryon import json

from alectryon.json import PlainSerializer
from .core import CLIDriver, EncodedDocument, Goal, Hypothesis, Message, Sentence, Text, UnexpectedError

class Lean4(CLIDriver):
    BIN = "leanInk"
    NAME = "Lean4"

    VERSION_ARGS = ("lV",)

    ID = "leanInk"
    LANGUAGE = "lean4"

    CLI_ARGS = ("analyze",)

    TMP_PREFIX = "leanInk_"
    LEAN_FILE_EXT = ".lean"
    LEAN_INK_FILE_EXT = ".leanInk"

    def run_leanInk_document(self, encoded_document):
        r""""
        Run LeanInk with encoded_document file.
        """
        with tempfile.TemporaryDirectory(prefix=self.TMP_PREFIX) as working_directory:
            inputFile = Path(working_directory) / os.path.basename(self.fpath)
            inputFile.write_bytes(encoded_document.contents)
            result = self.run_cli(more_args=[str(inputFile)])
            print(result)
            outputFile = inputFile.with_suffix(self.LEAN_FILE_EXT + self.LEAN_INK_FILE_EXT)
            content = outputFile.read_text(encoding="utf-8")
            print(content)
            jsonResult = json.loads(content)
            tupleResult = PlainSerializer.decode(jsonResult)
            print(tupleResult)
            return tupleResult

    def run_leanInk_filePath(self, fpath):
        r""""
        Run LeanInk with file at filePath.
        """
        fileExt = fpath.suffix

        if fileExt == self.LEAN_FILE_EXT:
            result = self.run_cli(more_args=[str(fpath)])
            print(result)
        else:
            raise UnexpectedError("Filepath provided to Lean 4 driver is not a valid .lean file!")

    def annotate(self, chunks):
        document = EncodedDocument(chunks, "\n", encoding="utf-8")
        string = document.contents.decode()
        return [self.run_leanInk_document(document)] # Atm this only works for a single chunk, we have to split them up again after evaluation.