#!/usr/bin/env python3
import json
import sys
from pathlib import Path
from pprint import pprint

recipes = Path(__file__).absolute().parent
sys.path.insert(0, str(recipes.parent))

libdir = recipes / "src"

# import alectryon.core; alectryon.core.DEBUG = True

def api_annotate():
    from alectryon.core import annotate
    annotated = annotate(["Check 1."], ("-Q", "{},lib".format(libdir)))
    pprint(annotated)

def annotated_to_json():
    from alectryon.core import annotate
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
    from alectryon.json import PlainSerializer
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import highlight_latex
    annotated = PlainSerializer.decode(json.loads(JS))
    for ltx in LatexGenerator(highlight_latex).gen(annotated):
        print("<latex>")
        print(ltx)
        print("</latex>")

def main():
    api_annotate()

if __name__ == '__main__':
    main()
