(*|
============================================
 Check for reST errors in literate comments
============================================

The ``lint`` backend in Alectryon checks a document for mistakes in embedded comments; to run it, use the following command::

    alectryon linter.v --backend lint # Coq+reST → JSON; produces ‘linter.lint.json’

.. unknown:: This is an error

This has a *missing delimiter warning.
|*)
