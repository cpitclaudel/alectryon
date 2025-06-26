===========
 Alectryon
===========

A library to process Coq and Lean 4 snippets embedded in text documents, showing goals and messages for each input sentence.  Also a literate programming toolkit.  The goal of Alectryon is to make it easy to write textbooks, blog posts, and other documents that mix interactive proofs and prose.

.. image:: etc/screenshot.svg
   :width: 100%
   :align: center

Alectryon is typically used in one of three ways:

- As a library, through its Python API

- As a Docutils/Sphinx extension, allowing you to include annotated snippets into your reStructuredText and Markdown documents.  During compilation, Alectryon collects all ``.. coq::`` code blocks, feeds their contents to Coq, and incorporates the resulting goals and responses into the final document.

- As a standalone compiler, allowing you to include prose delimited by special ``(*| … |*)`` comments directly into your Coq source files (in the style of coqdoc).  When invoked, Alectryon translates your Coq file into a reStructuredText document and compiles it using the standard reStructuredText toolchain.

For background information, check out the  `quickstart guide <https://systemf.epfl.ch/blog/alectryon/>`__ on the EPFL SYSTEMF blog, the `SLE2020 paper <https://doi.org/10.1145/3426425.3426940>`__ (open access) and its `live examples <https://alectryon-paper.github.io/>`__, or the `conference talk <https://www.youtube.com/watch?v=f8CKGoP3_us>`__.

Alectryon is free software under a very permissive license.  If you use it, please remember to `cite it <CITATION.bib>`__, and please let me know!

Some examples of use in the wild are linked `at the bottom of this page <gallery_>`_.  Please add your own work by submitting a PR!

Setup
=====

To install from OPAM and PyPI:
    | ``opam install "coq-serapi>=8.10.0+0.7.0"`` (from the `Coq OPAM archive <https://coq.inria.fr/opam-using.html>`__)
    | ``python3 -m pip install alectryon``

To install the latest version from Git, use ``python3 -m pip install git+https://github.com/cpitclaudel/alectryon.git``.  To install from a local clone, use ``python3 -m pip install .``.

**A note on dependencies**: the ``serapi`` module only depends on the ``coq-serapi`` OPAM package.  ``dominate`` is used in ``alectryon.html`` to generate HTML output, and ``pygments`` is used by the command-line application for syntax highlighting.  reStructuredText support requires ``docutils`` (and optionally ``sphinx``); Markdown support requires ``myst_parser`` (`docs <https://myst-parser.readthedocs.io/en/latest/index.html>`__); Coqdoc support requires ``beautifulsoup4``.  Support for Coq versions follows SerAPI; Coq ≥ 8.10 works well and ≥ 8.12 works best.

Usage
=====

As a standalone program
-----------------------

Recipes
~~~~~~~

Try these recipes in the ``recipes`` directory of this repository (for each task I listed two commands: a short one and a longer one making everything explicit):

Generate an interactive webpage from a literate Coq file with reST comments (Coqdoc style)
  .. code::

      alectryon literate_coq.v
      alectryon --frontend coq+rst --backend webpage literate_coq.v -o literate_coq.html

Generate an interactive webpage from a plain Coq file (Proof General style):
   .. code::

      alectryon --frontend coq plain.v
      alectryon --frontend coq --backend webpage plain.v -o plain.v.html

Generate an interactive webpage from a Coqdoc file (compatibility mode):
   .. code::

      alectryon --frontend coqdoc coqdoc.v
      alectryon --frontend coqdoc --backend webpage coqdoc.v -o coqdoc.html

Generate an interactive webpage from a reStructuredText document containing ``.. coq::`` directives (coqrst style):
   .. code::

      alectryon literate_reST.rst
      alectryon --frontend rst --backend webpage literate_reST.rst -o literate_reST.html

Generate an interactive webpage from a Markdown document written in the `MyST <https://myst-parser.readthedocs.io/en/latest/index.html>`__ dialect, containing ``.. coq::`` directives:
   .. code::

      alectryon literate_MyST.md
      alectryon --frontend md --backend webpage literate_MyST.md -o literate_MyST.html

Translate a reStructuredText document into a literate Coq file:
   .. code::

      alectryon literate_reST.rst -o literate_reST.v
      alectryon --frontend rst --backend coq+rst literate_reST.rst -o literate_reST.v

Translate a literate Coq file into a reStructuredText document:
   .. code::

      alectryon literate_coq.v -o literate_coq.v.rst
      alectryon --frontend coq+rst --backend rst literate_coq.v -o literate_coq.v.rst

Annotate snippets (``pre.alectryon``) within an HTML document:

   .. code::

      alectryon coq.html
      alectryon --frontend html --backend webpage coq.html -o coq.annotated.html

Annotate snippets (``\begin{alectryon}{coq}{unfold}``) within a TeX/LaTeX document (make sure to add ``\usepackage{alectryon}`` and ``\usepackage{pygments}`` to your preamble):

   .. code::

      alectryon coq.tex
      alectryon --frontend tex --backend latex coq.tex -o coq.annotated.tex

Record goals and responses for fragments contained in a JSON source file:
   .. code::

      alectryon fragments.v.json
      alectryon --frontend coq.json --backend json fragments.json -o fragments.v.io.json

Record goals and responses and format them as HTML for fragments contained in a JSON source file:
   .. code::

      alectryon fragments.v.json -o fragments.v.snippets.html
      alectryon --frontend coq.json --backend snippets-html fragments.json -o fragments.v.snippets.html

Command-line interface
~~~~~~~~~~~~~~~~~~~~~~

.. code::

   alectryon [-h] […]
             [--frontend {coq,coq+rst,coqdoc,html,json,md,rst,tex}]
             [--backend {coq,coq+rst,json,latex,rst,snippets-html,snippets-latex,webpage,…}]
             input [input ...]

Use ``alectryon --help`` for full command line details.

- Each ``input`` file can be ``.v`` (a Coq source file, optionally including reStructuredText in comments delimited by ``(*| … |*)``), ``.json`` (a list of Coq fragments), ``.rst`` (a reStructuredText document including ``.. coq::`` code blocks), or ``.md`` (a Markdown/MyST document including ``{coq}`` code blocks).  Each input fragment is split into individual sentences, which are executed one by one (all code is run in a single Coq session).

- One output file is written per input file.  Each frontend supports a subset of all backends.

  * With ``--backend webpage`` (the default for most inputs), output is written as a standalone webpage named ``<input>.html`` (for ``coq+rst`` inputs) or ``<input>.v.html`` (for plain ``coq`` inputs).
  * With ``--backend snippets-html``, output is written to ``<input>.snippets.html`` as a sequence of ``<pre class="alectryon-io">`` blocks, separated by ``<!-- alectryon-block-end -->`` markers (there will be as many blocks as entries in the input list if ``input`` is a ``.json`` file).
  * With ``--backend json``, output is written to ``<input>.io.json`` as a JSON-encoded list of Coq fragments (as many as in ``input`` if ``input`` is a ``.json`` file).  Each fragment is a list of records, each with a ``_type`` and some type-specific fields.  Here is an example:

    Input (``minimal.json``):
        .. code-block:: json

           ["Example xyz (H: False): True. (* ... *) exact I. Qed.",
            "Print xyz."]

    Output (``minimal.json.io.json``) after running ``alectryon --writer json minimal.json``:
        .. code-block:: js

           [ // A list of processed fragments
             [ // Each fragment is a list of records
               { // Each record has a type, and type-specific fields
                 "_type": "sentence",
                 "sentence": "Example xyz (H: False): True.",
                 "responses": [],
                 "goals": [ { "_type": "goal",
                              "name": "2",
                              "conclusion": "True",
                              "hypotheses": [ { "_type": "hypothesis",
                                                "name": "H",
                                                "body": null,
                                                "type": "False" } ] } ] },
               {"_type": "text", "string": " (* ... *) "},
               {"_type": "sentence", "sentence": "exact I.", "responses": [], "goals": []},
               {"_type": "text", "string": " "},
               {"_type": "sentence", "sentence": "Qed.", "responses": [], "goals": []} ],
             [ // This is the second fragment
               { "_type": "sentence",
                 "sentence": "Print xyz.",
                 "responses": ["xyz = fun _ : False => I\n     : False -> True"],
                 "goals": [] } ] ]

- The exit code produced by Alectryon indicates whether the conversion succeeded: ``0`` for success, ``1`` for a generic error, and ``10`` + the level of the most severe Docutils error if using a Docutils-based pipeline (hence ``10`` is debug, ``11`` is info, ``12`` is warning, ``13`` is error, and ``14`` is severe error).  Docutils errors at levels below `exit_status_level <https://docutils.sourceforge.io/docs/user/config.html#exit-status-level>`__ (default: 3) do not affect the exit code, so level ``10``, ``11``, and ``12`` are not used by default.

As a library
------------

Use ``alectryon.serapi.annotate(chunks: List[str])``, which returns an object with the same structure as the JSON above, but using objects instead of records with a ``_type`` field:

.. code-block:: python

    >>> from alectryon.serapi import annotate
    >>> annotate(["Example xyz (H: False): True. (* ... *) exact I. Qed.", "Check xyz."])
    [# A list of processed fragments
     [# Each fragment is a list of records (each an instance of a namedtuple)
      Sentence(contents='Example xyz (H: False): True.',
               messages=[],
               goals=[Goal(name=None,
                           conclusion='True',
                           hypotheses=[Hypothesis(names=['H'],
                                                  body=None,
                                                  type='False')])]),
      Text(contents=' (* ... *) '),
      Sentence(contents='exact I.', messages=[], goals=[]),
      Text(contents=' '),
      Sentence(contents='Qed.', messages=[], goals=[])],
     [# This is the second fragment
      Sentence(contents='Check xyz.',
               messages=[Message(contents='xyz\n     : False -> True')],
               goals=[])]]

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

To ensure that Coq blocks render properly, you'll need to tell your blogging platform to include ``alectryon.css``.  Using a git submodule or vendoring a copy of Alectryon is an easy way to ensure that this stylesheet is accessible to your blogging software.  Alternatively, you can use ``alectryon.cli.copy_assets``.  Assets are stored in ``alectryon.html.ASSETS.PATH``; their names are in ``alectryon.html.ASSETS.CSS`` and ``alectryon.html.ASSETS.JS``.

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

If left unset in your config file, the default role (the one you get with single backticks) will be set to ``:coq:``.  To get syntax highlighting for inline snippets, create a ``docutils.conf`` file with the `following contents <https://stackoverflow.com/questions/21591107/sphinx-inline-code-highlight>`_ along your ``conf.py`` file (see `below <docutils.conf_>`_ for details)::

   [restructuredtext parser]
   syntax_highlight = short

Setting options
~~~~~~~~~~~~~~~

Various settings are exposed as global constants in the docutils module:

- ``alectryon.docutils.LONG_LINE_THRESHOLD`` (same as ``--long-line-threshold``)
- ``alectryon.docutils.CACHE_DIRECTORY`` (same as ``--cache-directory``)
- ``alectryon.docutils.CACHE_COMPRESSION`` (same as ``--cache-compression``)
- ``alectryon.docutils.HTML_MINIFICATION`` (same as ``--html-minification``)
- ``alectryon.docutils.AlectryonTransform.SERTOP_ARGS`` (same as ``--sertop-arg``)

Controlling output
~~~~~~~~~~~~~~~~~~

The ``.. coq::`` directive takes a list of space-separated flags to control the way its contents are displayed:

- One option controls whether output is folded (``fold``) or unfolded (``unfold``).  When output is folded, users can reveal the output corresponding to each input line selectively.

- Multiple options control what is included in the output.

  - ``in``: Include input sentences (``no-in``: hide them)

  - ``goals``: Include goals (``no-goals``: hide them)

  - ``messages``: Include messages (``no-messages``: hide them)

  - ``hyps``: Include hypotheses (``no-hyps``: hide them)

  - ``out``: Include goals and messages (``no-out``: hide them)

  - ``all``: Include input, goals, and messages (``none``: hide them)

  - ``fails`` (for sentences expected to throw an error): Strip the `Fail` keyword from the input and remove the *The command has indeed failed with message:* prefix in the output. (``succeeds``: leave input and output as-is)

The default is ``all fold``, meaning that all output is available, and starts folded.  The exact semantics depend on the polarity of the first inclusion option encountered: ``x y z`` means the same as ``none x y z``, i.e. include ``x``, ``y``, ``z``, and nothing else; ``no-x no-y`` means ``all no-x no-y``, i.e. include everything except ``x`` and ``y``.

These annotations can also be added to individual Coq sentences (⚠ *sentences*, not lines), using special comments of the form ``(* .flag₁ … .flagₙ *)`` (a list of flags each prefixed with a ``.``):

.. code-block:: rst

   .. coq::

      Require Coq.Arith. (* .none *)             ← Executed but hidden
      Goal True. (* .unfold *)                   ← Goal unfolded
        Fail exact 1. (* .in .messages .fails *) ← Goal omitted
        Fail fail. (* .messages .fails *)        ← Error message shown, input hidden

More precise inclusion/exclusion is possible using the `marker-placement mini-language <marker-language_>`__ described below.  For example:

``-.h(Inhabited)``
  Hide all hypotheses that mention ``Inhabited``
``-.g#2.h#IHn``
  Hide hypothesis ``IHn`` in goal 2.
``-.g#2.h#*``
  Hide all hypotheses of goal 2.
``-.h#* .h#IHn``
  Show only hypothesis ``IHn``
``-.g#* .g#1 .g#3 .g{False}``
  Show only goals 1, 3, and any goal whose conclusion is ``False``.

Finally, you can use a ``[lang]=…`` annotation to chose which Pygments lexer to use to render part of a goal:

``.msg[lang]=haskell``
  Highlight the bodies of all messages produced by this sentence using the Haskell lexer.

**These last two features are experimental**; the syntax might change.

.. _marker-language:

Referring to subparts of a proof (the marker-placement mini-language)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each object in a proof (sentences, goals, messages, hypotheses, conclusions) can be referred to by giving a path that leads to it, written in CSS-inspired notation.  This makes it possible to selectively show, hide, or link to parts of the proof state.

In the example below, the markers ``[α]``, ``[β]``, and ``[γ]`` correspond to the paths listed below:

.. code-block:: coq

   Goal ∀ m n, m + n = n + m. [α]
     induction m; intros.
     - (* Base case *)
       【 n: ℕ ⊢ 0 + n = n + 0 [β] 】
       apply plus_n_O.
     - (* Induction *)
       【 m, n: ℕ; IHm: ∀ n: ℕ, m + n = n + m [γ]
          ⊢ S m + n = n + S m 】

- ``[α]``

  ``.s(Goal ∀)``
     Search for a sentence (``.s(…)``) by matching its contents.

- ``[β]``

  ``.s(Base case).ccl``
     Search for a sentence (``.s(…)``) matching ``Base case``, then match the conclusion (``.ccl``) of its first goal.

- ``[γ]``

  ``.s(Induction).h#IHm``
     Search for a sentence (``.s(…)``) matching ``Induction``, then match the hypothesis ``IHm`` by name  (``.h#…``) in the first goal.

  ``.s(Induction).g#1.h(m + n = n + m)``
     Search for a sentence (``.s(…)``) matching ``Induction``, select its first goal by number (``.g#…``), match the hypothesis ``IHm`` by searching for its contents (``.h(…)``).

The full architecture of a path is shown below for reference:

.. parsed-literal::

   .io#\ *name*                        ex: .io#\ **intro**
     A block of code whose name matches *name*.
   (.io is optional and defaults to the most recent code block.)

       .s(*pattern*)                  ex: .s(**Goal True**)
         Any sentence matching *pattern*.
       .s{*pattern*}                  ex: .s{**forall\*m\*n\*,**}
         Any sentence that completely matches *pattern*.

          .in
            The input part of the sentence.

          .msg
            Any message
          .msg(*str*)                 ex: .msg(**Closed under global context**)
            Any message whose text includes *str*.
          .msg{*pattern*}             ex: .msg{**\*[\*syntax\*]\***}
            Any message whose complete text matches *pattern*.

          .g#\ *id*                     ex: .g#\ **1**
            Goal number *id*.
          .g#\ *name*                   ex: .g#\ **base_case**
            The goal named *name* (`documentation <https://coq.inria.fr/refman/proofs/writing-proofs/proof-mode.html#coq:tacn.}>`__).
          .g(*str*)                   ex: .g(**True**)
            Any goal whose conclusion includes *str*.
          .g{*pattern*}               ex: .g{**\* ++ \* ++ \* = \***}
            Any goal whose complete conclusion matches *pattern*.
          (.g is optional and defaults to #1.)

              .ccl *|* .name
                The conclusion or name of the goal.

              .h#\ *name*               ex: .h#\ **IHn**
                 The hypothesis named *name*.
              .h(*str*)               ex: .h(**Permutation**)
                 Any hypothesis whose body or type includes *str*.
              .h{*pattern*}           ex: .h{**nat**}
                 Any hypothesis whose complete body or type matches *pattern*.

                  .type *|* .body *|* .name
                    The type or body or name of the hypothesis.

Plain search patterns (delimited by ``(…)``) are matched literally, anywhere in the term.  Other patterns (``{…}`` patterns and ``#…`` names) use ``fnmatch``-style `matching <https://docs.python.org/3/library/fnmatch.html>`__ (``?`` matches any character; ``*`` matches any sequence of characters; and ``[]`` matches a range of characters), and must match the whole term.  Hence:

- To match hypothesis ``H1`` but not ``H10`` nor ``IH1``, use ``.h#H1``.
- To match hypotheses of type ``nat``, but not of type ``list nat`` or ``nat -> nat``, use ``.h{nat}``
- To match hypotheses whole type or body includes ``Permutation`` anywhere, use ``.h(Permutation)`` or ``.h{*Permutation*}``.
- Etc.

As long as the search term does not contain special characters (``*?[]``), a plain search (``(…)``) is the same as an fnmatch-style search with wildcards on both sides (``{*…*}``).

Finally, you can attach  can attach arbitrary ``key``-``value`` to subparts of a goal matched using the marker-placement mini-language by appending ``[key]=value`` after the path.  This is useful with custom transforms and with the ``[lang]=…`` setting to customize highlighting for a given sentence or message.

**This feature is experimental**; the syntax might change.

Extra roles and directives
~~~~~~~~~~~~~~~~~~~~~~~~~~

For convenience, Alectryon includes a few extra roles and directives:

Markers and marker references
*****************************

The ``:mref:`` role (short for “marker reference”) can be used to point the reader to a sentence, a goal, or a hypothesis.  The argument is a search pattern written in the `marker-placement mini-language <marker-language_>`__; Alectryon locates the corresponding object in the input sent to the prover or in the prover's output, inserts a marker at that point, and replaces the reference with a link to that marker.

For example, the ``[γ]`` marker in the example above could be inserted using :literal:`:mref:\`.s(Induction).h#IHm\`` or :literal:`:mref:\`.s(Induction).g#1.h(m + n = n + m)\``.

By default markers refer to the most recent ``.. coq::`` block, but other blocks can be targeted by name by prepending ``.io#name`` to the argument of ``:mref:``.

Markers can be customized by setting the ``:counter-style:`` option on a custom role derived from ``:mref:``; for example, to use Devanagari numerals:

.. code-block:: rst

   .. role:: dref(mref)
      :counter-style: ० १ २ ३ ४ ५ ६ ७ ८ ९

More details and examples are given in `<recipes/references.rst>`__.

**This feature is experimental**: the syntax might change.

Quoted references to goal fragments
***********************************

The ``:mquote:`` role is similar to ``:mref:``, but it inserts a copy of the target instead of a link to it.  Targets may only be hypotheses, goal conclusions, or goal or hypothesis names.

For example, using :literal:`:mquote:\`.s(Induction).h#IHm.type\`` in the example above would print the type of ``IHm``, ``∀ n: ℕ, m + n = n + m`` whereas :literal:`:mref:\`.s(Induction).g#1.h(m + n = n + m).name\`` would produce only the name of the corresponding hypothesis, ``IHm``.

An ``.. mquote:`` directive is also available.  It places the quoted elements in a block and preserves indentation and newlines, unlike the ``:mquote:`` role (whose output appears inline).

More details and examples are given in `<recipes/references.rst>`__.

Output assertions
*****************

Sometimes it is desirable to check that the prover produced the right output, without displaying that output to the user.  In these cases, Alectryon's marker-placement mini-language can serve as a poor lad's unit test.  The ``massert`` directive takes one argument (a path prefix), and checks that each line of its body is a valid reference to part of a previous goal.

More details and examples are given in `<recipes/references.rst>`__.

Links to Coq identifiers
************************

``:coqid:`` can be used to link to the documentation or definition of a Coq identifier in an external file.  Some examples:

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

The ``alectryon.json`` module has facilities to cache the prover's output.  Caching has multiple benefits:

1. Recompiling documents with unchanged code is much faster, since Coq snippets do not have to be re-evaluated.
2. Deploying a website or recompiling a book does not require setting up a complete Coq development environment.
3. Changes in output can be inspected by comparing cache files.  Caches contain just as much information as needed to recreate input/output listings, so they can be checked-in into source control, making it easy to assess whether a Coq update meaningfully affects a document (it's easy to miss breakage or subtle changes in output otherwise, as when using the copy-paste approach or even Alectryon without caching).

To enable caching on the command line, chose a directory and pass it to ``--cache-directory``.  Alectryon will record inputs and outputs in individual JSON files (one ``.cache`` file per source file) in subdirectories of that folder.  You may pass the directory containing your source files if you'd like to store caches alongside inputs.

From Python, set ``alectryon.docutils.CACHE_DIRECTORY`` to enable caching.  For example, to store cache files alongside sources in Pelican, use the following code::

   import alectryon.docutils
   alectryon.docutils.CACHE_DIRECTORY = "content"

With a custom driver
--------------------

For advanced usage, or to customize Alectryon's command-line interface, you can use a custom driver.  Create a new Python file, and add the following to it:

.. code-block:: python

   from alectryon import cli
   … Any extension code here
   cli.main()

Extensions might include, registering additional docutils directives or roles with ``docutils.directives.register_directive`` and ``docutils.roles.register_canonical_role``, adding custom syntax highlighting for project-specific tokens using ``alectryon.pygments.add_tokens``, or even tweaking the operation of the Coq lexer in ``alectryon.pygments_lexer``, or monkey-patching parts of Alectryon's ``docutils`` module.

See `<recipes/alectryon_custom_driver.py>`__ for a concrete example.

Other proof assistants
======================

.. _lean4:

Lean 4
------

Alectryon has support for Lean 4. LeanInk (`LeanInk <https://github.com/leanprover/LeanInk>`_) is required to use Alectryon with Lean 4 files.
HTML and LaTeX output is supported from plain ``.lean`` source files and from ``.rst`` files.
The reStructuredText directive for Lean 4 is ``.. lean4::``, for Markdown/MyST files it is ``{lean4}``. The literate delimiter is ``/-!``:

- Include Lean 4 code in reStructuredText files like this:

  .. code-block:: rst

     Some reST prose.

     .. lean4::

        … some Lean 4 code

- Include reStructuredText prose in Lean 4 files like this:

  .. code-block:: lean

     … some Lean 4 code

     /-!
     Some reST prose.
     -/

See `<recipes/plain-lean4.lean>`__, `<recipes/lean4-tactics.rst>`__, `<recipes/lean4-tactics-myst.md>`__ and `<recipes/literate-lean4.lean>`__  for examples.

Lean 4 support was contributed by Niklas Bülow (@insightmind).

.. _lean3:

Lean 3
------

Alectryon has preliminary support for Lean 3.

Recording Lean's output and generating HTML or LaTeX is supported, from plain ``.lean`` files and from ``.rst`` files using the ``.. lean3::`` directive (as well as Markdown/MyST files using the ``{lean3}`` directive).  Language-agnostic features like caching work.  The literate delimiter is ``/-!``; in other words, you may write:

- Include Lean 3 code in reStructuredText files like this:

  .. code-block:: rst

     Some reST prose.

     .. lean3::

        … some Lean 3 code

- Include reStructuredText prose in Lean 3 files like this:

  .. code-block:: lean

     … some Lean 3 code

     /-!
     Some reST prose.
     -/

See `<recipes/plain-lean3.lean>`__ and `<recipes/lean3-tutorial.rst>`__ for examples.

The following features are missing:

- Concurrent processing of documents.  See the long comment above ``USE_THREADING`` in ``class Lean3`` of `<alectryon/lean3.py>`__.
- Support for literate Lean documents in Emacs/``alectryon-mode``.

Support for quoting snippets and displaying or hiding sentences is partial.

For a more detailed TODO list, see the header of `<alectryon/lean3.py>`__.

Polyglot documents
------------------

reStructuredText and Markdown documents compiled with Alectryon may combine all supported languages.  Code from each language is executed separately.  See `<recipes/polyglot.rst>`__ for an example.

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

To set SerAPI's arguments for all input files, modify ``AlectryonTransform.DRIVER_ARGS["sertop"]`` in ``alectryon.docutils``.  Here's an example that you could use in a Sphinx config file::

   from alectryon.docutils import AlectryonTransform
   AlectryonTransform.DRIVER_ARGS["sertop"] = ["-Q", "/coq/source/path/,LibraryName"]

Note that the syntax of ``DRIVER_ARGS["sertop"]`` is the one of ``sertop``, not the one of
``coqc`` (https://github.com/ejgallego/coq-serapi/issues/215).

Adding custom keywords
----------------------

You can use ``alectryon.pygments.add_tokens`` to specify additional highlighting
rules, such as custom tactic names.  See |help(add_tokens)|_ for more details.

.. |help(add_tokens)| replace:: ``help(alectryon.pygments.add_tokens)``
.. _help(add_tokens): alectryon/pygments.py

When compiling reStructuredText documents, you can add per-document highlighting rules to the docinfo section at the beginning of your document, like this:

.. code-block:: rst

   :alectryon/pygments/coq/tacn: intuition_eauto simplify invert
   :alectryon/pygments/coq/tacn-solve: map_tauto solve_eq

Interactivity
-------------

Most features in Alectryon's HTML output do not require JavaScript, but extra functionality (including keyboard navigation) can be added by loading ``assets/alectryon.js`` (this is done by default).

Scripts needed to unminify documents produced with ``--html-minification`` (see `below <minification_>`_) are bundled into the generated HTML and do not need to be loaded separately.

Authoring support
-----------------

The ``etc/elisp`` folder of this directory includes an Emacs mode, ``alectryon.el``, which makes it easy to switch between the Coq and reStructuredText views of a document.

.. _docutils.conf:

Docutils configuration
----------------------

You can set Docutils settings for your single-page reST or Coq+reST documents using a ``docutils.conf`` file.  See the `documentation <https://docutils.sourceforge.io/docs/user/config.html>`__ or the `example <recipes/docutils.conf>`__ in ``recipes/``.  For example, the following changes ``latex-preamble`` for the XeTeX backend to custom fonts::

   [xetex writer]
   latex-preamble:
     \setmainfont{Linux Libertine O}
     \setsansfont{Linux Biolinum O}
     \setmonofont[Scale=MatchLowercase]{Fira Code}

You can also use the `DOCUTILSCONFIG` `environment variable <https://docutils.sourceforge.io/docs/user/config.html#configuration-files>`__ to force alectryon to use a specific configuration file.

.. _minification:

Reducing page and cache sizes (experimental)
--------------------------------------------

Proofs with many repeated subgoals can generate very large HTML files and large caches.  In general, these files compress very well — especially with XZ and Brotli (often over 99%), less so with GZip (often over 95%).  But if you want to save space at rest, the following options may help:

- ``--html-minification``:  Replace repeated goals and hypotheses in the generated HTML with back-references and use more succinct markup.  Minimal Javascript is included in the generated page to resolve references and restore full interactivity.  Typical results::

     4.4M List.html          24.8M Ranalysis3.html
     1.4M List.min.html       452K Ranalysis3.min.html

- ``--cache-compression``: Compress caches (the default is to use XZ compression).  Typical results::

     3.2M List.v.cache       21M Ranalysis3.v.cache
      66K List.v.cache.xz    25K Ranalysis3.v.cache.xz

From Python, use ``alectryon.docutils.HTML_MINIFICATION = True`` and ``alectryon.docutils.CACHE_COMPRESSION = "xz"`` to enable minification and cache compression.

A minification algorithm for JSON is implemented in ``json.py`` but not exposed on the command line.

Diffing compressed caches
-------------------------

Compressed caches kept in a Git repository can be inspected by `automatically decompressing them <https://www.git-scm.com/docs/gitattributes#_performing_text_diffs_of_binary_files>`__ before computing diffs::

   # In $GIT_DIR/config or $HOME/.gitconfig:
   [diff "xz"]
     binary = true
     textconv = xzcat

   # In .gitattributes:
   *.cache.xz diff=xz

Building without SerAPI
-----------------------

Alectryon can compile documents using ``coqc``.  Sentences be split correctly, but goals and messages will not be collected, and error reporting will be less precise.  To use this feature, pass ``--coq-driver=coqc_time`` to Alectryon.

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

- If you just want to include math in reStructuredText or Markdown documents, docutils will generally do the right thing: it will generate code to load MathJaX from a CDN if you use the ``:math:`` role, and it leave that code out if you don't.

- If you want to render parts of your Coq code using MathJaX, things are trickier.  You need to identify which text to render as math by wrapping it into ``\( … \)`` markers; then add the ``mathjax_process`` class to the corresponding document nodes to force processing (otherwise MathJax ignores the contents of Alectryon's ``<pre>`` blocks); then trigger a recomputation.  See `<./recipes/mathjax.rst>`__ for an example and a more detailed discussion.

Suggested projects / TODOs
==========================

I do not work on the following tasks, but it would be very useful to complete them:

- Add support for converting to and from Markdown/MyST instead of reST.  This requires (1) changing ``literate.py`` to support reading and writing ``myst`` (a simple state machine); (2) adjusting ``cli.py`` to expose the new conversion functions; and (3) modifying ``etc/elisp/alectryon.el`` to make it convenient to switch back and forth.

- Upstream Alectryon's Coq highlighter for Pygments (it's an almost-complete rewrite of the original one).

- Add support for prettification in Pygments (display ``forall`` as ``∀``, etc.).  This require (1) Adding a pygments filter for prettification and (2) special-casing the rendering of prettified symbols somehow, so that copy-pasting them produces the original, unprettified rendering.

- Add support for diffing (displaying only changed hypotheses). See https://github.com/ejgallego/coq-serapi/issues/251

- Add support for ``mquote``-ing full goals and sentences.  This requires revamping the CSS (right now it assumes a specific nesting order of classes, and subparts of a proof state except the currently supported ones do not display correctly).

- Add support for quoting parts of another file, including its proof states: (1) design a mini-language to specify where to start and end, either in term of which definitions to select, or in terms of strings of text or regular expressions, or a combination (“definition of ``x`` within module ``A``” or “from ``induction …`` to ``solve [eauto]`` in proof of ``foo``”); (2) load documents that these directives refer to and embed the corresponding parts, compiling (with caching) as needed.

Adding support for new languages
========================================

Alectryon can be extended to support new languages.  Here is a rough blueprint on adding support for a fictional language `foo` (the variables mentioned below typically have docstrings offering further details):

1. Start in ``core.py`` and add your language to ``core.DRIVERS_BY_LANGUAGE``::

      "foo": {
          "foo_driver": (".foo", "Foo")
      },

   From here on and until support for your language is complete, running Alectryon will produce assertion failures; you can use these to guide your implementation or follow the guide below.

2. Add you language's file extensions to ``core.EXTENSIONS_BY_LANGUAGE``::

      "foo": (".foo", ".Foo")

3. Create a driver ``Foo`` for your language in file ``alectryon/foo.py`` (this is what ``.foo`` and ``Foo`` refer to in the snippet above)::

      from typing import Iterable, List, Optional
      from .core import DriverInfo, Driver, Text, Fragment

      class Foo(Driver):
          ID = "foo"
          def version_info(self) -> DriverInfo:
              return DriverInfo(name="Foo", version="1.0")
          def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
              return [[Text(c)] for c in chunks]

   The implementation given here does nothing; you'll want to replace it with one that actually runs code and records its output.  Alectryon has many helper classes for this purpose; refer to existing drivers and the docstrings of the base classes for more information.

4. Add transforms for your language to ``transforms.DEFAULT_TRANSFORMS``::

      "foo": [
          coalesce_text,
          read_io_comments("foo"),
          process_io_annots,
      ],

5. Add an entry to ``transforms._IO_COMMENT_RE`` to tell Alectryon how to identify IO annotations::

      "foo": r"[ \t]*[/][*]{}[*][/]",

6. Set up argument parsing for your language: add necessary flags in function ``build_parser`` of ``cli.py``, any required post-processing in ``post_process_arguments``, and add your language to ``DRIVER_ARGS_BY_NAME``::

      "foo": None,

7. Set up syntax highlighting (only if your language ID is unknown to Pygments) by adding an entry to ``pygments.CUSTOM_LEXER_ALIASES`` (``"text"`` is a no-op lexer)::

      "foo": "text",

8. Add literate support for your language by creating a language definition in ``literate.py``::

      class FooParser(LineParser):
          LIT_HEADER_RE = re.compile("^[ \t]*///[ ]?", re.MULTILINE)

      FOO = LineLangDef("foo", FooParser,
                        lit_header="///",
                        lit_header_re=FooParser.LIT_HEADER_RE)

   Tell Alectryon about your language by adding an entry to ``literate.LANGUAGES``::

      "foo": Foo,

.. _gallery:

Gallery
=======

- Arpan Agrawal, Emily First, Zhanna Kaufman, Tom Reichel, Shizhuo Zhang, Timothy Zhou, Alex Sanchez-Stern, Talia Ringer, Yuriy Brun, `Proofster: Automated Formal Verification <https://proofster.cs.umass.edu/>`__.
- Ana de Almeida Borges, `QRC1 in Coq — Formalizing a quantified modal logic <https://gitlab.com/ana-borges/QRC1-Coq/-/blob/ProofSociety/docs/slides/202112_ProofSocietyWorkshop/QRC1-Coq.pdf>`__
- Pierre Castéran, `Hydras, Ordinals & Co. — A library in Coq of entertaining formal mathematics <https://coq-community.org/hydra-battles/doc/hydras.pdf>`__ (PDF, using a custom `Alectryon driver <https://github.com/coq-community/hydra-battles/blob/master/doc/movies/driver.py>`__ to render snippets extracted from a large Coq development).
- Enrico Tassi, `Tutorial on the Elpi programming language <https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html>`__ (using a `custom Alectryon driver <https://github.com/LPCIC/coq-elpi/blob/master/etc/alectryon_elpi.py>`__ to highlight mixed Coq/ELPI code).
- Anton Trunov. `Introduction to Formal Verification course at CS Club <https://github.com/anton-trunov/csclub-coq-course-spring-2021>`__.
- Jean-Paul Bodeveix, Érik Martin-Dorel, Pierre Roux. `Types Abstraits et Programmation Fonctionnelle Avancée <https://github.com/pfitaxel/tapfa-coq-alectryon>`__.
- Li-yao Xia. `Tutorial: Verify Haskell Programs with hs-to-coq <https://www.cis.upenn.edu/~plclub/blog/2020-10-09-hs-to-coq/>`__.
- Silver Oak contributors. `Formal specification and verification of hardware, especially for security and privacy <https://project-oak.github.io/silveroak/demo/tutorial.html>`__.
- Philip Zucker. `Translating My Z3 Tutorial to Coq <https://www.philipzucker.com/translating-z3-to-coq/>`__.
- Li-yao Xia. `hakyll-alectryon: Hakyll extension for rendering Coq code using Alectryon <https://hackage.haskell.org/package/hakyll-alectryon>`__.
