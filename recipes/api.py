#!/usr/bin/env python3
"""
This file demonstrates a few uses of Alectryon's Python APIs.

To compile: python api.py > api.out # Direct API usage; produces ‘api.out’
"""

import json
import sys
from pathlib import Path
from pprint import pprint

recipes = Path(__file__).absolute().parent
sys.path.insert(0, str(recipes.parent))

libdir = recipes / "src"

# import alectryon.core; alectryon.core.DEBUG = True

def api_annotate():
    """Annotate a fragment of Coq code."""
    from alectryon.serapi import annotate
    annotated = annotate(["Check 1."], sertop_args=("-Q", "{},lib".format(libdir)))
    pprint(annotated)

def annotated_to_json():
    """Save results of annotation to JSON."""
    from alectryon.serapi import annotate
    from alectryon.json import PlainSerializer
    annotated = annotate([r"Goal True /\ True. split. ", "all: eauto."],
                         ("-Q", "{},lib".format(libdir)))
    print(json.dumps(PlainSerializer.encode(annotated)))

JS = """
[[{ "goals": [ { "hypotheses": [],
                 "conclusion": "True /\\\\ True",
                 "name": null, "_type": "goal" } ],
    "messages": [],
    "contents": "Goal True /\\\\ True.",
    "_type": "sentence" },
  { "contents": " ", "_type": "text" },
  { "goals": [ { "hypotheses": [],
                 "conclusion": "True",
                 "name": null, "_type": "goal" },
               { "hypotheses": [],
                 "conclusion": "True",
                 "name": null, "_type": "goal" } ],
    "messages": [],
    "contents": "split.",
    "_type": "sentence" },
  { "contents": " ", "_type": "text" }],
 [{ "goals": [],
    "messages": [],
    "contents": "all: eauto.",
    "_type": "sentence" }]]
"""

def latex_of_movie():
    """Load the result of a JSON → JSON conversion and write LaTeX snippets."""
    from alectryon.json import PlainSerializer
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import make_highlighter
    annotated = PlainSerializer.decode(json.loads(JS))
    highlighter = make_highlighter("latex", "coq")
    for ltx in LatexGenerator(highlighter).gen(annotated):
        print("<latex>")
        print(ltx)
        print("</latex>")

def main():
    api_annotate()
    print("=" * 80)
    annotated_to_json()
    print("=" * 80)
    latex_of_movie()

if __name__ == '__main__':
    main()
