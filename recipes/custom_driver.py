#!/usr/bin/env python3
import sys
from os.path import join, dirname

# This is an example of a custom driver: it exposes the same interface as
# Alectryon's usual CLI, but it sets the internal parameter pp_margin of SerAPI
# to a different value.

root = join(dirname(__file__), "..")
sys.path.insert(0, root)

from alectryon.cli import main
from alectryon.core import SerAPI

SerAPI.DEFAULT_PP_ARGS['pp_margin'] = 55

if __name__ == "__main__":
    main()
