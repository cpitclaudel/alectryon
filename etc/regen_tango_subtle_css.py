#!/usr/bin/env python3
"""Regenerate tango_subtle.css."""

import sys
from os.path import join, dirname, realpath
sys.path.insert(0, dirname(dirname(realpath(__file__))))

from alectryon.pygments import FORMATTER

pth = realpath('tango_subtle.css')
with open(pth, mode='w') as cssf:
    cssf.write(FORMATTER.get_style_defs('.highlight'))

print("Saved as {}".format(pth))
