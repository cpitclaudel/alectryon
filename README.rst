===========
 Alectryon
===========

A library to process Coq snippets embedded in documents, showing goals and messages for each Coq sentence.  Also a literate programming toolkit for Coq.  The goal of Alectryon is to make it easy to write textbooks, blog posts, and other documents that mix Coq code and prose.

Alectryon is typically used in one of three ways:

- As a library, through its Python API

- As a reStructuredText extension, allowing you to include annotated snippets into your reStructuredText documents.  During compilation, Alectryon collects all ``.. coq::`` blocks, feeds their contents to Coq, and incorporates the resulting goals and responses into the final document.

- As a standalone compiler, allowing you to include prose delimited by special ``(*| … |*)`` comments directly into your Coq source files (in the style of coqdoc).  When invoked, Alectryon translates your Coq file into a reStructuredText document and compiles it using the standard reStructuredText toolchain.

For background information, check out the  `quickstart guide <https://plv.csail.mit.edu/blog/alectryon.html>`__ on the MIT PLV blog, the `SLE2020 paper <https://doi.org/10.1145/3426425.3426940>`__ (open access) and its `live examples <https://alectryon-paper.github.io/>`__, or the `conference talk <https://www.youtube.com/watch?v=f8CKGoP3_us>`__.

Alectryon is free software under a very permissive license.  If you use it, please remember to `cite it <https://pit-claudel.fr/clement/papers/alectryon-SLE20.bib>`__, and please let me know!

Some examples of use in the wild are linked `at the bottom of this page <#gallery>`__.  Please add your own work by submitting a PR!

Setup
=====

To install from OPAM and PyPI:
    | ``opam install "coq-serapi>=8.10.0+0.7.0"`` (from the `Coq OPAM archive <https://coq.inria.fr/opam-using.html>`__)
    | ``python3 -m pip install alectryon``

**A note on dependencies**: the core library only depends on ``coq-serapi`` from OPAM.  ``dominate`` is used in ``alectryon.html`` to generate HTML output, and ``pygments`` is used by the command-line application for syntax highlighting.  reStructuredText support requires ``docutils`` (and optionally ``sphinx``); Coqdoc support requires ``beautifulsoup4``.  Support for Coq versions follows SerAPI; Coq ≥ 8.10 works well and ≥ 8.12 works best.

Usage
=====

As a standalone program
-----------------------

Recipes
~~~~~~~

Try these recipes in the ``recipes`` directory of this repository (for each task I listed two commands: a short one and a longer one making everything explicit):

Generate an interactive webpage from a literate Coq file with reST comments (Coqdoc style):
   .. code::

      alectryon literate.v
      alectryon --frontend coq+rst --backend webpage literate.v -o literate.html

Generate an interactive webpage from a plain Coq file (Proof General style):
   .. code::

      alectryon --frontend coq plain.v
      alectryon --frontend coq --backend webpage plain.v -o plain.v.html

Generate an interactive webpage from a Coqdoc file (compatibility mode):
   .. code::

      alectryon --frontend coqdoc literate.v
      alectryon --frontend coqdoc --backend webpage literate.v -o literate.html

Compile a reStructuredText document containing ``.. coq::`` blocks (coqrst style):
   .. code::

      alectryon literate.v.rst
      alectryon --frontend rst --backend webpage literate.v.rst -o literate.html

Translate a reStructuredText document into a literate Coq file:
   .. code::

      alectryon literate.v.rst -o literate.v
      alectryon --frontend rst --backend coq+rst literate.v.rst -o literate.v

Translate a literate Coq file into a reStructuredText document:
   .. code::

      alectryon literate.v -o literate.v.rst
      alectryon --frontend coq+rst --backend rst literate.v -o literate.v.rst

Record goals and responses for fragments contained in a JSON source file:
   .. code::

      alectryon fragments.json
      alectryon --frontend json --backend json fragments.json -o fragments.io.json

Record goals and responses and format them as HTML for fragments contained in a JSON source file:
   .. code::

      alectryon fragments.json -o fragments.snippets.html
      alectryon --frontend json --backend snippets-html fragments.json -o fragments.snippets.html

Command-line interface
~~~~~~~~~~~~~~~~~~~~~~

.. code::

   alectryon [-h] […]
              [--frontend {coq,coq+rst,json,rst}]
              [--backend {coq,coq+rst,json,snippets-html,webpage}]
              input [input ...]

- Each ``input`` file can be ``.v`` (a Coq source file, optionally including reStructuredText in comments delimited by ``(*| … |*)``), ``.json`` (a list of Coq fragments), or ``.rst`` (a reStructuredText document including ``.. coq::`` blocks).  Each input fragment is split into individual sentences, which are executed one by one (all code is run in a single Coq session).

- One output file is written per input file.  Each frontend supports a subset of all backends.

  * With ``--backend webpage``, output is written as a standalone webpage named ``<input>.html`` (for ``coq+rst`` inputs) or ``<input>.v.html`` (for plain ``coq`` inputs).  This is useful for debugging and to get a quick sense of how Alectryon works.
  * With ``--backend snippets-html``, output is written to ``<input>.snippets.html`` as a sequence of ``<pre class="alectryon-io">`` blocks, separated by ``<!-- alectryon-block-end -->`` markers (there will be as many blocks as entries in the input list if ``input`` is a ``.json`` file).
  * With ``--writer json``, output is written to ``<input>.io.json`` as a JSON-encoded list of Coq fragments (as many as in ``input`` if ``input`` is a ``.json`` file).  Each fragment is a list of records, each with a ``_type`` and some type-specific fields.  Here is an example:

    Input (``minimal.json``):
        .. code-block:: json

           ["Example xyz (H: False): True. (* ... *) exact I. Qed.",
            "Print xyz."]

    Output (``minimal.json.io.json``) after running ``alectryon --writer json minimal.json``:
        .. code-block:: js

            [ // A list of fragments
              [ // Each fragment is a list of records
                { // Each record has a type, and type-specific fields
                  "_type": "sentence",
                  "sentence": "Example xyz (H: False): True.",
                  "responses": [],
                  "goals": [
                    {
                      "_type": "goal",
                      "name": "2",
                      "conclusion": "True",
                      "hypotheses": [
                        {
                          "_type": "hypothesis",
                          "name": "H",
                          "body": null,
                          "type": "False"
                        }
                      ]
                    }
                  ]
                },
                {"_type": "text", "string": " (* ... *) "},
                {"_type": "sentence", "sentence": "exact I.", "responses": [], "goals": []},
                {"_type": "text", "string": " "},
                {"_type": "sentence", "sentence": "Qed.", "responses": [], "goals": []}
              ],
              [
                {
                  "_type": "sentence",
                  "sentence": "Print xyz.",
                  "responses": ["xyz = fun _ : False => I\n     : False -> True"],
                  "goals": []
                }
              ]
            ]

Use ``alectryon --help`` for full command line details.

As a library
------------

Use ``alectryon.core.annotate(chunks: List[str])``, which returns an object with the same structure as the JSON above, but using objects instead of records with a ``_type`` field:

.. code-block:: python

    >>> from alectryon.core import annotate
    >>> annotate(["Example xyz (H: False): True. (* ... *) exact I. Qed.", "Print xyz."])
    [
        [CoqSentence(sentence='Example xyz (H: False): True.',
                     responses=[],
                     goals=[
                         CoqGoal(
                             name='2',
                             conclusion='True',
                             hypotheses=[
                                 CoqHypothesis(name='H',
                                               body=None,
                                               type='False')
                             ])
                     ]),
         CoqText(string=' (* ... *) '),
         CoqSentence(sentence='exact I.', responses=[], goals=[]),
         CoqText(string=' '),
         CoqSentence(sentence='Qed.', responses=[], goals=[])],

        [CoqSentence(sentence='Print xyz.',
                     responses=['xyz = fun _ : False => I\n     : False -> True'],
                 goals=[])]
    ]

The results of ``annotate`` can be fed to ``alectryon.html.HtmlGenerator(highlighter).gen()`` to generate HTML (with CSS classes defined in ``alectryon.css``).  Pass ``highlighter=alectryon.pygments.highlight_html`` to use Pygments, or any other function from strings to ``dominate`` tags to use a custom syntax highlighter.

As a docutils or Sphinx module
------------------------------

With blogs (Pelican, Nikola, Hugo, etc.)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Include the following code in your configuration file to setup Alectryon's ``docutils`` extensions:

.. code-block:: python

    import alectryon.docutils
    alectryon.docutils.setup()

This snippet registers a ``.. coq::`` directive, which feeds its contents to Alectryon and displays the resulting responses and goals interleaved with the input and a ``:coq:`` role for highlighting inline Coq code.  It also replaces the default Pygments highlighter for Coq with Alectryon's improved one, and sets `:coq:` as the default role.  See |help(docutils)|_ for more information.

To ensure that Coq blocks render properly, you'll need to tell your blogging platform to include ``alectryon.css``.  Using a git submodule or vendoring a copy of Alectryon is an easy way to ensure that this stylesheet is accessible to your blogging software.  Alternatively, you can use ``alectryon.html.copy_assets``.  Assets are stored in ``alectryon.html.ASSETS.PATH``; their names are in ``alectryon.html.ASSETS.CSS`` and ``alectryon.html.ASSETS.JS``.

By default, Alectryon's docutils module will raise warnings for lines over 72 characters.  You can change the threshold or silence the warnings by adjusting ``alectryon.docutils.LONG_LINE_THRESHOLD``.  With `Pelican <https://github.com/getpelican/pelican>`_, use the following snippet to make warnings non-fatal:

.. code-block:: python

   DOCUTILS_SETTINGS = {
       'halt_level': 3, # Error
       'warning_stream': None # stderr
   }

.. |help(docutils)| replace:: ``help(alectryon.docutils)``
.. _help(docutils): alectryon/docutils.py

I test regularly with Pelican; other systems will likely need minimal adjustments.

With Sphinx
~~~~~~~~~~~

For Sphinx, add the following to your ``conf.py`` file:

.. code-block:: python

   extensions = ["alectryon.sphinx"]

If left unset in your config file, the default role (the one you get with single backticks) will be set to ``:coq:``.  To get syntax highlighting for inline snippets, create a docutils.conf file with the `following contents <https://stackoverflow.com/questions/21591107/sphinx-inline-code-highlight>`_ along your ``conf.py`` file::

   [restructuredtext parser]
   syntax_highlight = short

Controlling output
~~~~~~~~~~~~~~~~~~

The ``.. coq::`` directive takes a list of space-separated flags to control the way its contents are displayed:

- One option controls whether output is folded (``fold``) or unfolded (``unfold``).  When output is folded, users can reveal the output corresponding to each input line selectively.

- Multiple options control what is included in the output.
  - ``in``: Include input sentences (``no-in``: hide them)
  - ``goals``: Include goals (``no-goals``: hide them)
  - ``messages``: Include messages (``no-messages``: hide them)
  - ``out``: Include goals and messages (``no-out``: hide them)
  - ``all``: Include input, goals, and messages (``none``: hide them)

The default is ``all fold``, meaning that all output is available, and starts folded.  The exact semantics depend on the polarity of the first inclusion option encountered: ``x y z`` means the same as ``none x y z``, i.e. include ``x``, ``y``, ``z``, and nothing else; ``no-x no-y`` means ``all no-x no-y``, i.e. include everything except ``x`` and ``y``.

These annotations can also be added to individual Coq sentences (⚠ *sentences*, not lines), using special comments of the form ``(* .flag₁ … .flagₙ *)`` (a list of flags each prefixed with a ``.``):

.. code-block:: rst

   .. coq::

      Require Coq.Arith. (* .none *)      ← Executed but hidden
      Goal True. (* .unfold *)            ← Goal unfolded
        Fail exact 1. (* .in .messages *) ← Goal omitted
        Fail fail. (* .messages *)        ← Error message shown, input hidden

Extra roles and directives
~~~~~~~~~~~~~~~~~~~~~~~~~~

For convenience, alectryon includes a few extra roles and directives:

- ``:coqid:`` can be used to link to the documentation or definition of a Coq identifier in an external file.  Some examples:

  - :literal:`:coqid:\`Coq.Init.Nat.even\`` → `Coq.Init.Nat.even <https://coq.inria.fr/library/Coq.Init.Nat.html#even>`__
  - :literal:`:coqid:\`Coq.Init.Nat#even\`` → `even <https://coq.inria.fr/library/Coq.Init.Nat.html#even>`__
  - :literal:`:coqid:\`a predicate <Coq.Init.Nat.even>\`` → `a predicate <https://coq.inria.fr/library/Coq.Init.Nat.html#even>`__
  - :literal:`:coqid:\`Coq.Arith.PeanoNat#\`` → `Coq.Arith.PeanoNat <https://coq.inria.fr/library/Coq.Arith.PeanoNat.html#>`__
  - :literal:`:coqid:\`a library <Coq.Arith.PeanoNat#>\`` → `a library <https://coq.inria.fr/library/Coq.Arith.PeanoNat.html#>`__
  - :literal:`:coqid:\`Coq.Arith.PeanoNat#Nat.Even\`` → `Nat.Even <https://coq.inria.fr/library/Coq.Arith.PeanoNat.html#Nat.Even>`__
  - :literal:`:coqid:\`a predicate <Coq.Arith.PeanoNat#Nat.Even>\`` → `a predicate <https://coq.inria.fr/library/Coq.Arith.PeanoNat.html#Nat.Even>`__

  By default, ``:coqid:`` only knows how to handle names from Coq's standard library (that is, names starting with ``Coq.``, which get translated to links pointing to https://coq.inria.fr/library/).  To link to other libraries, you can add entries to ``alectryon.docutils.COQ_IDENT_DB_URLS``, a list of tuples containing a prefix and a templated URL.  The URL can refer to ``$modpath``, the part before the last ``#`` or ``.`` in the fully qualified name, and ``$ident``, the part after the last ``#`` or ``.``.  Here is an example::

     ("My.Lib", "https://your-url.com/$modpath.html#$ident")

  Alternatively, you can inherit from ``:coqid:`` to define new roles.  The following defines a new ``:mylib:`` role, which assumes that its target is part of ``My.Lib``::

     .. role:: mylib(coqid)
        :url: https://your-url.com/My.Lib.$modpath.html#$ident

Caching
~~~~~~~

The ``alectryon.json`` module has facilities to cache annotations.  Caching has multiple benefits:

1. Recompiling documents with unchanged code is much faster, since Coq snippets do not have to be re-evaluated.
2. Deploying a website or recompiling a book does not require setting up a complete Coq development environment.
3. Changes in output can be inspected by comparing cache files.  Caches contain just as much information as needed to recreate input/output listings, so they can be checked-in into source control, making it easy to assess whether a Coq update meaningfully affects a document (it's easy to miss breakage or subtle changes in output otherwise, as when using the copy-paste approach or even Alectryon without caching).

To enable caching, chose a directory to hold cache files and assign its path to  ``alectryon.docutils.CACHE_DIRECTORY`` (it can be the same directory as the one containing your source files, if you'd like to store caches alongside inputs).  Alectryon will record inputs and outputs in individual JSON files (one ``.cache`` file per source file) in subdirectories of the ``CACHE_DIRECTORY`` folder.

Tips
====

Prettification
--------------

Programming fonts with ligatures are a good way to display prettified symbols without resorting to complex hacks.  Good candidates include *Fira Code* and *Iosevka* (with the latter, add ``.alectryon-io { font-feature-settings: 'XV00' 1; }`` to your CSS to pick Coq-specific ligatures).

Passing arguments to SerAPI
---------------------------

When using the command line interface, you can use the ``-I``, ``-Q``, ``-R`` and ``--sertop-arg`` flags to specify custom SerAPI arguments, like this::

   alectryon -R . Lib --sertop-arg=--async-workers=4

When compiling reStructuredText documents, you can add custom SerAPI arguments in a docinfo section at the beginning of your document, like this:

.. code-block:: rst

   :alectryon/serapi/args: -R . Lib -I mldir

To set SerAPI's arguments for all input files, modify ``AlectryonTransform.SERTOP_ARGS`` in ``alectryon.docutils``.  Here's an example that you could use in a Sphinx config file::

   from alectryon.docutils import AlectryonTransform
   AlectryonTransform.SERTOP_ARGS = ["-Q", "/coq/source/path/,LibraryName"]

Note that the syntax of ``SERTOP_ARGS`` is the one of ``sertop``, not the one of
``coqc`` (https://github.com/ejgallego/coq-serapi/issues/215).

Adding custom keywords
----------------------

You can use ``alectryon.pygments.add_tokens`` to specify additional highlighting
rules, such as custom tactic names.  See |help(add_tokens)|_ for more details.

.. |help(add_tokens)| replace:: ``help(alectryon.pygments.add_tokens)``
.. _help(add_tokens): alectryon/pygments.py

When compiling reStructuredText documents, you can add per-document highlighting rules to the docinfo section at the beginning of your document, like this:

.. code-block:: rst

   :alectryon/pygments/tacn: intuition_eauto simplify invert
   :alectryon/pygments/tacn-solve: map_tauto solve_eq

Interactivity
-------------

Alectryon's HTML output doesn't require JavaScript for basic interactivity, but ``assets/alectryon.js`` implements keyboard navigation.

Authoring support
-----------------

The ``etc/elisp`` folder of this directory includes an Emacs mode, ``alectryon.el``, which makes it easy to switch between the Coq and reStructuredText views of a document.

Docutils configuration
----------------------

You can set Docutils settings for your single-page Coq+reST documents using a ``docutils.conf`` file.  See the `documentation <https://docutils.sourceforge.io/docs/user/config.html>`__ or the `example <recipes/docutils.conf>`__ in ``recipes/``.  For example, the following changes ``latex-preamble`` for the XeTeX backend to select a custom monospace font::

   [xetex writer]
   latex-preamble:
     \setmainfont{Linux Libertine O}
     \setsansfont{Linux Biolinum O}
     \setmonofont[Scale=MatchLowercase]{Fira Code}

Caching
-------

To use Alectryon's caching facilities independently of its ``docutils`` module, instantiate the ``FileCache`` class of ``alectryon.json``.

Building without Alectryon
--------------------------

The ``alectryon.minimal`` Python module provides trivial shims for Alectryon's roles and directives, allowing you continue compiling your documents even if support for Alectryon stops in the future.

Including custom JS or CSS in Alectryon's output
------------------------------------------------

For single-page documents, you can use a ``.. raw::`` directive:

.. code:: rst

   .. raw:: html

      <script src="https://d3js.org/d3.v5.min.js" charset="utf-8"></script>
      <script src="https://dagrejs.github.io/project/dagre-d3/latest/dagre-d3.js"></script>

      <link rel="stylesheet" href="rbt.css">
      <script type="text/javascript" src="rbt.js"></script>

For documents with more pages, you can either move the ``.. raw`` part to a separate file and ``.. include`` it, or you can use a custom driver: create a new file ``driver.py`` and use the following:

.. code:: python

   import alectryon.html
   import alectryon.cli

   alectryon.html.ADDITIONAL_HEADS.append('<link rel="stylesheet" href="…" />')
   alectryon.cli.main()

But for large collections of related documents, it's likely better to use Sphinx (or some other similar engine).  In that case, you can use Sphinx' built-in support for additional JS and CSS: ``app.add_js_file(js)`` and ``app.add_css_file(css)``.

Special case: MathJax
~~~~~~~~~~~~~~~~~~~~~

MathJax is a JavaScript library for rendering LaTeX math within webpages.  Properly configuring it can be a bit tricky.

- If you just want to include math in reStructuredText documents, docutils will generally do the right thing: it will generate code to load MathJaX from a CDN if you use the ``:math:`` role, and it leave that code out if you don't.

- If you want to render parts of your Coq code using MathJaX, things are trickier: you need to use Javascript to:

  1. Configure MathJax to stop ignoring ``<pre>`` blocks by adding a ``MathJax = …`` `config block <http://docs.mathjax.org/en/latest/web/configuration.html>`__::

        MathJax = {}
        MathJax.options = { processHtmlClass: 'alectryon-io' };

  2. Add ``\( … \)`` math markers to tell MathJax where to look (see `<./recipes/mathjax.rst>`__ for an example)::

        MathJax.startup = {
            pageReady: function () {
                // … Custom code to add \( … \) delimiters
                return MathJax.startup.defaultPageReady(); // Then run MathJax
            }
        }

  3. Ensure that these definitions are processed *before* MathJax itself is loaded, since it's not easy to `reconfigure MathJax after loading it <http://docs.mathjax.org/en/latest/web/configuration.html#configuring-mathjax-after-it-is-loaded>`__.  Concretely, this means either adding ``defer`` to the MathJax ``<script>`` tag, moving the configuration to a separate script loaded before MathJax, or moving the MathJax ``<script>`` to the end of the file (past the configuration above).

     The problem is that docutils automatically inserts the MathJax ``<script>`` tag for you if you use some math in the document, so you don't have much control over it (if you don't have any ``:math:`` roles then there's no problem: you can include the MathJax script yourself as explained in the previous section).

  Alectryon already configures docutils to load MathJax with the ``defer`` option, so the steps above should work reliably when using Alectryon in standalone mode (point [3.] is already taken care of).

  Sphinx loads MathJax in ``async`` mode by default, so the above won't work reliably, and the ``mathjax3_config`` option is not always enough (it only supports simple types, not functions; see `Sphinx issue 9450 <https://github.com/sphinx-doc/sphinx/issues/9450>`__).  Instead, put the configuration above in a separate script and include it in ``html_js_files`` with sufficiently low priority (must be < 500).  See `<recipes/sphinx/conf.py>`__ and `<recipes/sphinx/_static/mathjax_config.js>`__ for an example (you can inline the body of the script directly in ``conf.py``).

  For other processors, such as Pelican, then you need to either move your configuration to a separate file and make sure that it is loaded first, as in Sphinx, or find a way to defer ``MathJax``.  The following usually works::

     from docutils.writers._html_base import HTMLTranslator
     HTMLTranslator.mathjax_script = '<script type="text/javascript" defer src="%s"></script>\n'

.. _gallery:

Gallery
=======

- Jean-Paul Bodeveix, Érik Martin-Dorel, Pierre Roux. `Types Abstraits et Programmation Fonctionnelle Avancée <https://github.com/pfitaxel/tapfa-coq-alectryon>`__
- Silver Oak contributors. `Formal specification and verification of hardware, especially for security and privacy. <https://project-oak.github.io/silveroak/demo/tutorial.html>`__
- Philip Zucker. `Translating My Z3 Tutorial to Coq <https://www.philipzucker.com/translating-z3-to-coq/>`__
- Li-yao Xia. `hakyll-alectryon: Hakyll extension for rendering Coq code using Alectryon <https://hackage.haskell.org/package/hakyll-alectryon>`__
