===============
 Major changes
===============

Version 2.0.0
=============

- Alectryon is now compatible with Rocq 9, Docutils 22, Sphinx 9.1, Pygments 2.19, and Python 3.9+.

- Alectryon now supports the two main Rocq LSP servers: VsRocq and coq-lsp.  VsRocq is the default for Rocq files, replacing SerAPI; it is reasonably well supported. Coq-lsp is experimental.  SerAPI is still supported for Coq versions < 9.  Known limitations are documented in VsRocq issues `#1198`_, `#1199`_, `#1201`_, `#1203`_, `#1204`_, `#1205`_, `#1206`_, `#1209`_, and `#1210`_; help is welcome to fix these issues and improve VsRocq support (for now, Alectryon bundles mitigation for most of them). [c28fb384, 830f41e2, 8c4f256f, ffffc913, 81dcd0ac, 9ff1e752]

- Settings from ``_RocqProject`` files are now recognized and applied.  This makes it easy to configure dependencies (``-Q …``), warnings (``-arg -w -arg -notation-for-abbreviation``), printing parameters (``-arg -set -arg "'Printing Depth=30'"``, ``-arg -set -arg "'Printing Width=55'"``), etc.

- Alectryon now has experimental support for Dafny, including a literate-programming mode (conversions between Dafny files with ``///`` comments and reST/Markdown documents) and semantic highlighting via the Dafny LSP server. [1f8370e, ca1b0784, 6bdcd555]

- Alectryon now supports literate programming in Markdown in addition to reStructuredText.  Markdown files (``.md``, ``.myst``) containing ``{coq}`` code blocks can be rendered to LaTeX or HTML through Docutils, or converted to Rocq files (``.v``) with ``(*| … |*)`` comments using the ``coq`` backend, and vice versa using the ``coq+md`` frontend.  [e17fe936, 85632183, 46f037b5, c5253aaa, 901247db]

- HTML and LaTeX files containing Rocq snippets can now be ingested by Alectryon and rewritten to insert recorded goals and prover outputs, using the new ``html`` and ``latex`` frontends.  This makes it possible to process code blocks embedded in HTML or LaTeX documents without going through Docutils. [49f7ec1a, cc169410]

- ``alectryon-mode`` now supports Dafny, Lean 4, and ``markdown-mode`` buffers. [bec2575f, 32f0e1e5, b7313ae1, cf948f95]

- Exporting to LaTeX now displays hypotheses bodies in addition to hypothesis types. [7eb70b00, 20e30444]

- A ``noop`` driver is now available for all languages, skipping prover execution entirely. [929066a1]

Bug fixes
---------

- (HTML) Do not add an HTML4 xmlns attribute to HTML5 outputs. [fab53849]

- (LaTeX) Fix an incompatibility with the hyperref package by namespacing alectryon macros (``\al{xyz}`` expands to ``alectryon@xyz``). [716454dc]

- (LaTeX export) Prevent narrow spaces in ``\alectryonInline{}`` macros from propagating to ``\begin{alectryon}`` environments. [76fc9e07]

- (LaTeX) Fix a compatibility issue with the ``longtable`` package. [b5c3bfb2]

Breaking changes
----------------

- (CLI) Error messages from Rocq now include column information. [1fdcd006]

- (Rocq) The default Coq driver is now ``vsrocq`` (was ``sertop``).  SerAPI is still available using ``--coq-driver sertop``. [81dcd0ac]

- (Rocq) The ``coqdoc`` frontend now invokes ``rocq doc`` instead of ``coqdoc``. [829fde48]

- (Rocq) The default printing width and depth are now determined by Rocq, not Alectryon.  To recover the previous behavior, create a ``_RocqProject`` file with ``-arg -set -arg "'Printing Depth=30'"`` and ``-arg -set -arg "'Printing Width=55'"``.

- (Lean) The literate-programming comment delimiters for Lean files have changed from ``/-! … !-/`` to ``/-| … |-/``. [278fb597]

- (LaTeX) The ``alectryon`` and ``alectryon@inline`` environments have been simplified to make it easier to redefine them. [2be83289]

- (LaTeX) All Alectryon macros are now wrapped in ``\al`` / ``\Al`` commands (e.g., ``\al{xyz}`` expands to ``alectryon@xyz``). [424709a5]

- (HTML) The HTML class ``alectryon-wsp`` has been renamed to ``alectryon-txt``. [872e83d1]

.. _#1198: https://github.com/rocq-prover/vsrocq/issues/1198
.. _#1199: https://github.com/rocq-prover/vsrocq/issues/1199
.. _#1201: https://github.com/rocq-prover/vsrocq/issues/1201
.. _#1203: https://github.com/rocq-prover/vsrocq/issues/1203
.. _#1204: https://github.com/rocq-prover/vsrocq/issues/1204
.. _#1205: https://github.com/rocq-prover/vsrocq/issues/1205
.. _#1206: https://github.com/rocq-prover/vsrocq/issues/1206
.. _#1209: https://github.com/rocq-prover/vsrocq/issues/1209
.. _#1210: https://github.com/rocq-prover/vsrocq/issues/1210

1.5.0
=====

- Alectryon is now compatible with Python 3.10, Sphinx 6.1.3, Docutils 0.19, and Pygments 2.14 (other reasonably recent versions should still work). [c6db43a, 40ff2af, 578a1db, 39535f4]

- Alectryon now has partial support for Lean 3 and 4.  The ``.lean`` file extension is now associated with Lean 4; Lean 3 files should use ``.lean3``.  [GH-76, GH-64] [27ea5b8, 90bd555, 601174b]

Bug fixes
---------

- (Emacs) Fix initialization of ``-executable`` when installing from MELPA. [5505e00]

- (Emacs) Don't assume that ``flyspell`` is loaded when starting ``alectryon-mode``. [8a1f305]

- (CLI) ``--long-line-threshold 0`` can now be used to disable long-line warnings. [e317465]

Breaking changes
----------------

- (Pygments) ``replace_builtin_coq_lexer()`` has been renamed to ``replace_builtin_lexers()``. [7b26c83]

Version 1.4.0
=============

- JSON recordings (produced by ``--backend json``) can now be used as inputs to generate webpages or highlighted snippets. [c69b08ee]

- Alectryon's cache format has changed to support documents with multiple languages.  Caches created with previous versions of Alectryon can still be read and do not need to be regenerated. [d376077b]

- Alectryon can now compile Coq documents without running proofs nor recording Coq's output.  This is useful for quick experimentation. [GH-52] [6f4ae202]

- Alectryon can now compile Coq documents with ``coqc`` instead of ``SerAPI``.  The results do not include goals or messages.  This is useful when trying out a version of Coq that SerAPI does not support yet. [GH-60] [735e72b9]

- Per-document Coq syntax-highlighting rules added to the docinfo section at the beginning of each document are now prefixed with ``alectryon/pygments/coq/`` instead of ``alectryon/pygments/`` (the legacy prefix is still supported). [3a9ffe6d]

- A new extension of the marker-placement mini-language allows authors to attach properties to parts of a proof; for example, ``.. coq:: .s(Extraction).msg[lang]=haskell`` highlights all messages produced by ``Extraction`` commands using the Haskell lexer instead of the usual Coq lexer. [409fa6c3]

- A new ``massert`` directive silently provides a simple form of unit-testing by silently checking a collection of marker-placement references, thus confirming that the prover's output matches user-provided search patterns. [bc2d8a42] [GH-63]

- A new ``mquote`` directive complements the ``mquote`` role by allowing authors to quote parts of a proof as a block (the ``mquote`` role generates inline text). [e0c9eda5]

- Alectryon now accepts a ``--pygments-style`` flag to chose which Pygments code-highlighting style to use.  It also honors the Sphinx configuration option ``pygments_style``. [GH-58] [63539edd]

- Alectryon now exits with an informative error code (``10`` + the level of the most severe Docutils error). [GH-57] [dffde22c]

Breaking changes
----------------

- Multiple APIs have been generalized to allow working with languages other than Coq and drivers other than SerAPI.  In particular, ``docutils.AlectryonTransform.SERTOP_ARGS`` is now ``docutils.AlectryonTransform.DRIVER_ARGS['sertop']`` [735e72b9]; ``transforms.DEFAULT_TRANSFORMS`` is now ``transforms.DEFAULT_TRANSFORMS["coq"]`` [370b8206]; docinfo headers for custom highlighting now use the prefix ``alectryon/pygments/coq/`` instead of ``alectryon/pygments/`` [a58a0449] (backwards-compatible); caches are now partitioned by language [d376077b] (backwards-compatible); ``html.gen_banner`` now takes a list of ``DriverInfo`` instances (renamed from ``GeneratorInfo`` in [2ce6c0a4]) instead of a single one [d376077b]; ``--backend json`` now writes files named ``.v.io.json`` instead of ``.io.json``; and ``--frontend json`` is now ``--frontend coq.json`` [] (backwards-compatible).

- SerAPI-specific parts of the ``core`` module have been moved to a new ``serapi`` module. [91058a61]

- The Pygments stylesheets generated by Alectryon were renamed from ``tango_subtle.sty`` and ``tango_subtle.css`` to ``pygments.sty`` and ``pygments.css`` to reflect the fact that the style is not hardcoded any more. [9c15544f]  Instead, these stylesheets are now generated dynamically based on the style chosen using the ``--pygments-style`` flag or the ``pygments_style`` option in ``docutils.conf``. [63539edd]  The files ``assets/tango_subtle.*`` have been removed. [cea4ed47]

Bug fixes
---------

- Alectryon will now copy assets (CSS and STY files) in the directory of the *output* file (rather than that of the *input* file) when no ``--output-directory`` is specified.  This only matters if an output file is specified using ``-o`` (otherwise, the directory of the output file is the same as the input file, so the new behavior matches the old one). [6a35af22]

Version 1.3.1
=============

- Spacing and line breaks in LaTeX documents generated by Alectryon are now more consistent, especially in ``no-out`` blocks. [91fc735, bc4f408]

Bug fixes
---------

- Fix line breaking between long hypotheses in LuaLaTeX. [cf0596c]

Version 1.3.0
=============

- **EXPERIMENTAL** A new mini-language lets authors show or hide specific sentences, hypotheses, and goals within a fragment of Coq code.  The same language can be used in conjunction with a new ``:mref:`` role to place markers and create references to a subpart of a goal, and with a new ``:mquote:`` role to replicate subparts of a goal inline. [8a02bce, 14f45b7, 4f91484] [GH-36, GH-2]

- Alectryon's LaTeX preamble has been rewritten to improve line breaking between and within hypotheses. [3325d55]

- ``.. coq::`` directives now accept ``:class:`` and ``:name:`` arguments. [df6ff35, 7cf03d6]

- A new ``--long-line-threshold`` flag controls the line length over which Alectryon will issue “long line” warnings. [0286051]

- A new ``--cache-compression`` flag enables compression of generated cache files.  This typically yields space savings of over 95%. [GH-35]

- A new ``--html-minification`` flag enables the generation of more compact HTML files.  Minified HTML files use backreferences to refer to repeated goals and hypotheses (these backreferences are resolved at display time using Javascript) and more succinct markup (full markup is rebuilt dynamically at page load).  This typically saves 70-90% of the generated file size, and nearly as much on HTML generation time on page load times. [GH-35]

- HTML5, XeLaTeX and LuaLaTeX outputs are now supported (``--latex-dialect``, ``--html-dialect``). [c576ae8]

Bug fixes
---------

- Fix parsing of reST docinfo fields for custom highlighting (`:alectryon/pygments/…:`). [33df0f2]

Breaking changes
----------------

- Improvements to goals rendering in HTML may cause very slight alignment changes.  Use ``.alectryon-io .goal-separator { height: calc(1em + 1px); }`` to revert to the previous alignment (modulo rounding errors).

- The LaTeX markup of hypotheses has changed: ``alectryon@hyp`` is now a macro, not an environment.

- Docutils option ``"syntax_highlight"`` now defaults to ``"short"`` when using Alectryon's CLI or its custom HTML writer.  That is, inline `:coq:` roles now produce short-form CSS Pygments class names when processed using ``alectryon.docutils`` or the CLI. [72749bd]

- The HTML markup for ``alectryon-io`` blocks has been simplified to save space in generated files (may affect third-party stylesheets).  Specifically, the ``.highlight`` class is now applied to whole ``.alectryon-io`` blocks; ``.hyp-body-block`` and ``.hyp-type-block`` are now ``.hyp-body`` and ``.hyp-type``; and the following classes have been removed: ``.goal-hyp`` (use ``.goal-hyps > span``), ``.hyp-name`` (use ``.goal-hyps var``), ``.hyp-body`` (use ``.hyp-body > span``), ``.hyp-type`` (use ``.hyp-type > span``), ``.hyp-punct`` (use ``.goal-hyps b`` or ``.hyp-type > b`` and ``.hyp-body > b``), ``.alectryon-output-stycky-wrapper`` (use ``.alectryon-output > div``), ``.alectryon-extra-goal-label`` (use ``.alectryon-extra-goals > .goal-separator``). [59563f1, dc4b128, 28a004e]

- ``json.Cache`` in module ``alectryon.json`` now takes arbitrary ``metadata`` instead of ``sertop_args``. [56ca103]

- ``json_of_annotated`` and ``annotated_of_json`` in module ``alectryon.json`` are now ``PlainSerializer.encode`` and ``PlainSerializer.decode``. [c1076cc]

Version 1.2.1
=============

Bug fixes
---------

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
