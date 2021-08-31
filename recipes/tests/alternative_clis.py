"""
This file demonstrates how to call Alectryon's through Docutils CLI.

To run::

  $ python alternative_clis.py > alternative_clis.out
      # CLIs; produces ‘alternative_clis.out’
"""
import sys
from io import BytesIO, TextIOWrapper

from alectryon import cli, literate

def run(cmd, args, stdin):
    sys.argv = ["({})".format(cmd.__name__), "-", *args]
    sys.stdin = TextIOWrapper(BytesIO(stdin.encode("utf-8")))
    print("== {} ==".format(cmd.__name__))
    try:
        cmd()
        sys.exit(0)
    except SystemExit as e:
        print("-- exit: {} --\n".format(e.code))

def main():
    COQ_INPUT = "Check nat."
    REST_INPUT = literate.coq2rst(COQ_INPUT)
    run(cli.rstcoq2html, ["--no-header"], COQ_INPUT)
    run(cli.coqrst2html, ["--no-header"], REST_INPUT)
    run(cli.rstcoq2latex, [], COQ_INPUT)
    run(cli.coqrst2latex, [], REST_INPUT)

if __name__ == '__main__':
    main()
