#!/usr/bin/env python
# Pretty-print a JSON file, removing all newlines from all strings.
# This is useful to compare Alectryon cache files.

import json
import re
import sys
from pathlib import Path

JSON = str | list["JSON"] | dict[str, "JSON"] | float | int
def cleanup(js: JSON) -> JSON:
    match js:
        case dict():
            return {k: cleanup(v) for k, v in js.items()}
        case list():
            return [cleanup(o) for o in js]
        case str():
            return re.sub(r"\s+", " ", js, flags=re.UNICODE)
        case _:
            return js

path = Path(sys.argv[1])
dirty = path.read_bytes()
try:
    js: JSON = json.loads(dirty)
    js = cleanup(js)
    clean = json.dumps(js, indent=2, ensure_ascii=False, sort_keys=False)
    print(clean)
except:
    print(f"!! Could not read {path}")
    print(dirty)
