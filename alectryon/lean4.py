# TODO: Add license

import tempfile
import os
import shutil
import subprocess
from pathlib import Path
from alectryon import json

from alectryon.json import PlainSerializer
from .core import CLIDriver, EncodedDocument, indent

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
    LAKE_TMP_FILE_PATH = "lakefile.lean"

    def run_leanInk_CLI(self, working_directory, more_args=()):
        cmd = [self.resolve_driver(self.binpath),
               *self.CLI_ARGS, *self.user_args, *more_args]
        self._debug_start(cmd)
        p = subprocess.run(cmd, capture_output=True, cwd=working_directory, check=False, encoding=self.CLI_ENCODING)
        if p.returncode != 0:
            MSG = "Driver {} ({}) exited with code {}:\n{}"
            raise ValueError(MSG.format(self.NAME, self.binpath, p.returncode,
                                        indent(self._proc_out(p), "   ")))
        return p.stdout

    def run_leanInk_document(self, encoded_document):
        r"""
        Run LeanInk with encoded_document file.
        """
        with tempfile.TemporaryDirectory(prefix=self.TMP_PREFIX) as temp_directory:
            inputFile = Path(temp_directory) / os.path.basename(self.fpath)
            inputFile.write_bytes(encoded_document.contents)
            working_directory = temp_directory
            if self.lake_file_path != None:
                working_directory = os.path.dirname(os.path.realpath(self.lake_file_path))
                self.user_args += ["--lake", self.LAKE_TMP_FILE_PATH]
            result = self.run_leanInk_CLI(working_directory, more_args=[str(os.path.abspath(inputFile))])
            print(result)
            outputFile = inputFile.with_suffix(self.LEAN_FILE_EXT + self.LEAN_INK_FILE_EXT)
            content = outputFile.read_text(encoding="utf-8")
            jsonResult = json.loads(content)
            tupleResult = PlainSerializer.decode(jsonResult)
            return tupleResult
    
    def resolve_lake_arg(self):
        r"""
        Remove lake argument from user_args for manual evaluation.
        """
        new_user_args = []
        for (index, arg) in enumerate(self.user_args, start=0):
            if arg == "--lake":
                self.lake_file_path = self.user_args[index + 1]
                new_user_args = self.user_args[index + 2:]
                break
            else:
                new_user_args += arg
        self.user_args = new_user_args

    def annotate(self, chunks):
        document = EncodedDocument(chunks, "\n", encoding="utf-8")
        self.resolve_lake_arg()
        return [self.run_leanInk_document(document)] # Atm this only works for a single chunk, we have to split them up again after evaluation.