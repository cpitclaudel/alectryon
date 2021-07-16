===============
 Major changes
===============

Unreleased
==========

- A new ``--long-line-threshold`` flag controls the line length over which Alectryon will issue “long line” warnings. [0286051]

- A new ``--cache-compression`` flag enables compression of generated cache files.  This typically yields space savings of over 95%. [GH-35]

- A new ``--html-minification`` flag enables the generation of more compact HTML files.  Minified HTML files use backreferences to refer to repeated goals and hypotheses (these backreferences are resolved at display time using Javascript) and more succinct markup (full markup is rebuilt dynamically at page load).  This typically saves 70-90% of the generated file size, and nearly as much on HTML generation time on page load times. [GH-35]

- HTML5, XeLaTeX and LuaLaTeX outputs are now supported (``--latex-dialect``, ``--html-dialect``). [c576ae8]

Breaking changes
----------------

- Docutils option ``"syntax_highlight"`` now defaults to ``"short"`` when using Alectryon's CLI or its custom HTML writer.  That is, inline `:coq:` roles now produce short-form CSS Pygments class names when processed using ``alectryon.docutils`` or the CLI. [72749bd]

- The HTML markup for ``alectryon-io`` blocks has been simplified to save space in generated files (may affect third-party stylesheets). [59563f1]

- ``json.Cache`` in module ``alectryon.json`` now takes arbitrary ``metadata`` instead of ``sertop_args``. [56ca103]

- ``json_of_annotated`` and ``annotated_of_json`` in module ``alectryon.json`` are now ``PlainSerializer.encode`` and ``PlainSerializer.decode``. [c1076cc]

Version 1.2.1
=============

- Fix an API breakage introduced by the implementation LaTeX export (``AlectryonPostTransform`` was only registered for Docutils and Sphinx, but not for other document processors like Pelican; the updated implementation registers it unconditionally). [4cc19b9]

Version 1.2
===========

- Caching is now supported for all documents, not just those processed through docutils (``--cache-directory``). [c3dfa6b]

- (Experimental) LaTeX export now works for full reST and Coq documents, not just snippets. [GH-47]

Version 1.1
===========

- Alectryon is now on PyPI. [GH-46]

- `alectryon.el` is now on MELPA. [https://github.com/melpa/melpa/pull/7554]

Breaking changes
----------------

- CSS classes have been renamed from ``.coq-…`` to ``.alectryon-…``.
- CSS class ``alectryon-header`` is now ``alectryon-banner``.
- The undocumented ``alectryon-header`` has been removed.
