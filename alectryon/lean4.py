# TODO: Add license

from .core import CLIDriver, EncodedDocument, Positioned, Position, Sentence, Text

class Lean4(CLIDriver):
    BIN = "leanInk"
    NAME = "Lean4"

    ID = "leanInk"
    LANGUAGE = "lean4"

    CLI_ARGS = ("analyze")

    def annotate(self, chunks):
        print("Hello from Lean4 driver")
        return [] # TODO: Actually return something usefull