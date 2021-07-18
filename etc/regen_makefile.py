#!/usr/bin/env python3

import sys
import re
from pathlib import Path

CMD_RE = re.compile(r"""
    (?:^[ ]+(?=alectryon)|To[ ]compile:|[$])[ ]*(?P<cmd>[^\s]+)[ ]+
    (?P<args>.*?)\s+ # Allows newline
    [#][ ]+
    (?P<comment>.+?)[;,][ ]+produces[ ]+
    ‘(?P<out>.+?)’
""", re.VERBOSE | re.MULTILINE)

def parse_rules(path: str):
    with open(path) as f:
        contents = f.read()
    for m in CMD_RE.finditer(contents):
        yield m.groupdict()

TEMPLATE = """\
# {comment}
{out}: {fpath}{dir_deps}
	{cmd}\
"""

def gen_rule(fpath, outdir, params):
    params["cmd"] = params["cmd"] \
        .replace("alectryon", "$(alectryon)")

    params["cmd"] = (params["cmd"] + " " + params["args"]) \
        .replace(fpath.name, "$<") \
        .replace(params["out"], "$@") \
        .replace("python", "$(PYTHON)")

    params["out"] = str(outdir / params["out"])

    needs_outdir = "$(alectryon)" not in params["cmd"]
    params["dir_deps"] = " | {}".format(outdir) if needs_outdir else ""

    return params["out"], TEMPLATE.format(fpath=fpath, **params)

HEADER = """\
# -*- makefile -*-
### Auto-generated with etc/regen_recipes_makefile.py ###
### Do not edit! ###

{outdir}:
	mkdir -p $@
"""

FOOTER = """\
{all_targets}: out_dir := {outdir}

targets += {all_targets}\
"""

def main():
    outdir = Path(sys.argv[1])
    print(HEADER.format(outdir=outdir))

    all_targets = []
    for fname in sorted(sys.argv[2:]):
        src, targets = Path(fname), []
        for params in parse_rules(src):
            dst, rule = gen_rule(src, outdir, params)
            targets.append(dst)
            print(rule)
        if targets:
            all_targets.extend(targets)
            print()

    print(FOOTER.format(all_targets=" ".join(all_targets), outdir=outdir))

if __name__ == '__main__':
    main()
