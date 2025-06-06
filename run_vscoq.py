import sys
from alectryon.transforms import pretty_print_fragments
from alectryon.vscoqFinal import VsCoq
from alectryon.core import Document

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python test_vscoq.py <file.v>")
        sys.exit(1)

    filepath = sys.argv[1]

    with VsCoq(fpath=filepath) as api:
        with open(api.fpath, "r") as f:
            content = f.read()
            result = api.annotate([content])
            pretty_print_fragments(result[0])
