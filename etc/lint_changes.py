#!/usr/bin/env python3
# Check for incorrect commit IDs and update automatically

# FILTER_BRANCH_SQUELCH_WARNING=1 git filter-branch  -f --tree-filter "make lint-changes; git add CHANGES.rst" START..HEAD

import re
import subprocess
import shlex
import sys

SINGLE_HASH = re.compile(r"[a-f0-9]{6,}")
ANNOT = re.compile(r"\[{}(, *{})*\]".format(
    SINGLE_HASH.pattern, SINGLE_HASH.pattern))

def shell(cmd):
    with subprocess.Popen(shlex.split(cmd), encoding="utf-8",
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE) as p:
        stdout, stderr = p.communicate()
        if p.returncode != 0:
            print(stderr, file=sys.stderr, end='')
            return None
        return stdout

def sub1(m):
    sha = m.group()
    if shell(f'git merge-base --is-ancestor "{sha}" HEAD') is None:
        print(f"{sha} is not an ancestor of HEAD", file=sys.stderr)
        if shell(f'git cat-file -e "{sha}^{{commit}}"') is not None:
            msg = shell(f'git log --format=%s -n 1 "{sha}"').strip()
            print(f"             {msg}", file=sys.stderr)
            for line in shell('git log --format="%h %s"').splitlines():
                if msg in line:
                    print(f"    {line}", file=sys.stderr)
                    return next(SINGLE_HASH.finditer(line)).group()
    return sha

def subn(m):
    return SINGLE_HASH.sub(sub1, m.group())

def main():
    # changes = 0
    with open(sys.argv[1]) as f:
        contents = f.read()
    with open(sys.argv[1], mode="w") as f:
        f.write(ANNOT.sub(subn, contents))

if __name__ == '__main__':
    main()
