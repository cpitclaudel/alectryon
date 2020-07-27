#!/usr/bin/env python3
"""Regenerate tango_subtle.css."""

import sys
from subprocess import check_call
from os.path import join, dirname, realpath

root = dirname(dirname(realpath(__file__)))
sys.path.insert(0, root)

from alectryon.pygments import FORMATTER, LATEX_FORMATTER

def css():
    pth = realpath(join(root, 'assets/tango_subtle.css'))
    min_pth = realpath(join(root, 'assets/tango_subtle.min.css'))
    with open(pth, mode='w') as cssf:
        cssf.write(FORMATTER.get_style_defs('.highlight'))
    print("Saved as {}".format(pth))
    check_call(["cleancss", pth, "-o", min_pth])
    print("Minified as {}".format(min_pth))

def ltx():
    pth = realpath(join(root, 'assets/tango_subtle.sty'))
    with open(pth, mode='w') as ltxf:
        ltxf.write(LATEX_FORMATTER.get_style_defs())
    print("Saved as {}".format(pth))

if __name__ == '__main__':
    css()
    ltx()
