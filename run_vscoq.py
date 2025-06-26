#!/usr/bin/env python3
import sys
from pprint import pprint
from pathlib import Path
from alectryon.vscoqFinal import VsCoq
import alectryon.core

alectryon.core.DEBUG = True

if __name__ == "__main__":
    vscoq = VsCoq(fpath=sys.argv[1])
    pprint(vscoq.annotate([Path(vscoq.fpath).read_text()]))
