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

    LAKE_FILE_PATH = None
    LAKE_TMP_FILE_PATH = "lakefile.lean"
    LEAN_TOOLCHAIN_PATH = "lean-toolchain"

    def create_toolchain_file(self, working_directory):
        lean_toolchain_file = Path(working_directory) / os.path.basename(self.LEAN_TOOLCHAIN_PATH)
        version = "leanprover/lean4:nightly-2021-12-03" # TODO: get this from leanInk
        lean_toolchain_file.write_bytes(version.encode("utf-8")) 

    def copy_lake_file(self, working_directory):
        if self.LAKE_FILE_PATH == None: return
        lake_out_file = Path(working_directory) / os.path.basename(self.LAKE_TMP_FILE_PATH)
        lake_in_file = Path(self.LAKE_FILE_PATH)
        shutil.copyfile(lake_in_file, lake_out_file)
        self.user_args += ["--lake", str(self.LAKE_TMP_FILE_PATH)]

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
        with tempfile.TemporaryDirectory(prefix=self.TMP_PREFIX) as working_directory:
            inputFile = Path(working_directory) / os.path.basename(self.fpath)
            inputFile.write_bytes(encoded_document.contents)
            self.copy_lake_file(working_directory)
            self.create_toolchain_file(working_directory)
            result = self.run_leanInk_CLI(working_directory, more_args=[str(os.path.basename(inputFile))])
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
                self.LAKE_FILE_PATH = self.user_args[index + 1]
                new_user_args = self.user_args[index + 2:]
                break
            else:
                new_user_args += arg
        self.user_args = new_user_args

    def annotate(self, chunks):
        document = EncodedDocument(chunks, "\n", encoding="utf-8")
        self.resolve_lake_arg()
        return [self.run_leanInk_document(document)] # Atm this only works for a single chunk, we have to split them up again after evaluation.