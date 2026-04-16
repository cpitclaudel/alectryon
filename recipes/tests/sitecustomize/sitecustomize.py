"""Set up a test environment."""

import os

# Set Lean3 binary to "lean3" to avoid conflicts
from alectryon.lean3 import Lean3
Lean3.BIN = "lean3"

# Install the typeguard hook
if os.environ.get("TYPEGUARD"):
    from typeguard import install_import_hook
    install_import_hook("alectryon")
