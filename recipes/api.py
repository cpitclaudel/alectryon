#!/usr/bin/env python3
import sys
from os.path import join, dirname

root = join(dirname(__file__), "..")
sys.path.insert(0, root)

from alectryon.core import annotate

# import alectryon.core
# alectryon.core.DEBUG = True

def main():
    print(annotate(["Check 1."], ("-Q", "{},logical_name".format(root))))

if __name__ == '__main__':
    main()
