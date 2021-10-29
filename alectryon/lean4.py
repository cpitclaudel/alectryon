# TODO: Add license

from .core import CLIDriver, EncodedDocument, Positioned, Position, Sentence, Text

class Lean4(CLIDriver):
    BIN = "leanInk"
    NAME = "Lean4"

    ID = "leanInk"
    LANGUAGE = "lean4"

    CLI_ARGS = ("analyze")