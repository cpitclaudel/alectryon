r"""Misc unit tests

To run::

   $ python unit.py | sed 's/\(tests\?\) in [0-9.]\+s$/\1/g' > unit.py.out
       # Unit tests; produces ‘unit.py.out’
"""

import contextlib
import io
import unittest
import sys
from tempfile import TemporaryDirectory
from pathlib import Path

import warnings
warnings.simplefilter("always")

@contextlib.contextmanager
def redirected_std():
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        yield (out, err)

class Json(unittest.TestCase):
    @staticmethod
    def cache(chunks, driver, root, docpath, metadata, compression):
        from alectryon.json import FileCache
        cache = FileCache(root, docpath, metadata, compression)
        cache.update(chunks, driver)

    def test_validation(self):
        from alectryon.serapi import SerAPI
        with TemporaryDirectory() as cache_root:
            cache_root = Path(cache_root)
            docpath = cache_root / "test.v"

            driver = SerAPI(fpath=docpath)

            chunks = ["Goal True."]
            metadata = {}
            self.cache(chunks, driver, cache_root, docpath, {}, "none")

            with redirected_std() as (out, _):
                metadata = driver.metadata
                self.cache(chunks, driver, cache_root, docpath, metadata, "none")
                self.assertRegex(out.getvalue().strip(), r"\AOutdated metadata.*\Z")

            with redirected_std() as (out, _):
                chunks = ["Goal False."]
                self.cache(chunks, driver, cache_root, docpath, metadata, "none")
                self.assertRegex(out.getvalue().strip(), r"\AOutdated contents.*\Z")

            with redirected_std() as (out, _):
                self.cache(chunks, driver, cache_root, docpath, metadata, "xz")
                self.assertRegex(out.getvalue().strip(), r"\ARecompression requested.*\Z")

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
