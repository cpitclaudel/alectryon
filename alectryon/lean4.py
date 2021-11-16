# Copyright © 2021 Niklas Bülow
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
            jsonResult = json.loads(content)
            tupleResult = PlainSerializer.decode(jsonResult)
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