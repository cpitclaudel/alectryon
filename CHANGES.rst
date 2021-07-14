===============
 Major changes
===============

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
