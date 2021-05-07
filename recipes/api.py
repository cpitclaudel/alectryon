#!/usr/bin/env python3
import json
import sys
from os.path import join, dirname
from pprint import pprint

root = join(dirname(__file__), "..")
sys.path.insert(0, root)

# import alectryon.core
# alectryon.core.DEBUG = True

def api_annotate():
    from alectryon.core import annotate
    annotated = annotate(["Check 1."], ("-Q", "{},logical_name".format(root)))
    pprint(annotated)

def annotated_to_json():
    from alectryon.core import annotate
    from alectryon.json import json_of_annotated
    annotated = annotate([r"Goal True /\ True. split. ", "all: eauto."],
                         ("-Q", "{},logical_name".format(root)))
    print(json.dumps(json_of_annotated(annotated)))

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
    from alectryon.json import annotated_of_json
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import highlight_latex
    annotated = annotated_of_json(json.loads(JS))
    for ltx in LatexGenerator(highlight_latex).gen(annotated):
        print("<latex>")
        print(ltx)
        print("</latex>")

def main():
    api_annotate()

if __name__ == '__main__':
    main()
