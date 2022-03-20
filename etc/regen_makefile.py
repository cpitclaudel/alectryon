#!/usr/bin/env python3

import sys
import re
from pathlib import PurePosixPath as Path
from fnmatch import fnmatch

CMD_RE = re.compile(r"""
    (?:^[ ]+(?=alectryon)|To[ ]compile:|[$])[ ]*(?P<cmd>[^\s]+)[ ]+
    (?P<args>(?:.|\\\n)*?) # Allow escaped newlines in arguments
    \s+[#][ ]+ # Allows newline before "#"
    (?P<comment>.+?)[;,][\n ]+produces[ ]+
    ‘(?P<out>.+?)’
""", re.VERBOSE | re.MULTILINE)

def parse_rules(path: str):
    with open(path, encoding="utf-8") as f:
        contents = f.read()
    for m in CMD_RE.finditer(contents):
        yield m.groupdict()

RULE_TEMPLATE = """\
# {comment}
{out}: {fpath}{dir_deps}
	{cmd}
{prefix}_targets += {out}\
"""

def escape(s):
    return s.replace("$", "$$").replace("#", "##")

CUSTOM_DRIVER_RE = re.compile(r"\b(alectryon_[a-z_]+[.]py)\b")

def gen_rule(fpath, prefix, outdir, params):
    params = { k: escape(v) for (k, v) in params.items() }

    # Remove escaped newlines
    params["args"] = re.sub(r"\s+\\\n\s+", " ", params["args"])

    params["cmd"] = (params["cmd"] + " " + params["args"]) \
        .replace("alectryon ", "$(alectryon) ") \
        .replace("python ", "$(PYTHON) ") \
        .replace(params["out"], "$@") \
        .replace(fpath.name, "$<")

    params["cmd"] = CUSTOM_DRIVER_RE.sub(r"\1 $(alectryon_opts)", params["cmd"])

    params["out"] = str(outdir / params["out"])

    needs_outdir = "$(alectryon)" not in params["cmd"]
    params["dir_deps"] = " | {}/".format(outdir) if needs_outdir else ""

    return params["out"], RULE_TEMPLATE.format(fpath=fpath, prefix=prefix, **params)

HEADER = """\
# -*- makefile -*-
### Auto-generated with etc/regen_makefile.py ###
### Do not edit! ###

{outdir}/:
	mkdir -p $@

{prefix}_targets :=
"""

FOOTER = """\
$({prefix}_targets): out_dir := {outdir}
targets += $({prefix}_targets)\
"""

EXCLUDED_SOURCES = {
    "*docutils.conf",
    "*.v.cache",
    "flycheck_*.py",
    "custom_stylesheet.css"
}

def main():
    prefix = sys.argv[1]
    outdir = Path(sys.argv[2])
    print(HEADER.format(prefix=prefix, outdir=outdir))

    all_targets = []
    for fname in sorted(sys.argv[3:]):
        src, targets = Path(fname), []
        if any(fnmatch(src.name, pattern) for pattern in EXCLUDED_SOURCES):
            continue
        for params in parse_rules(src):
            dst, rule = gen_rule(src, prefix, outdir, params)
            targets.append(dst)
            print(rule)
        if targets:
            all_targets.extend(targets)
            print()
        else:
            print("Not sure how to compile {}".format(fname), file=sys.stderr)

    print(FOOTER.format(prefix=prefix, outdir=outdir))

if __name__ == '__main__':
    main()
