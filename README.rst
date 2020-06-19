===========
 Alectryon
===========

A library to process Coq snippets embedded in documents, showing goals and messages for each Coq sentence.  The goal of Alectryon is to make it easy to write papers, webpages, and other documents that show bits of Coq code along with their output.

Setup
=====

Dependencies (OCaml, Python 3):
    ``opam install coq-serapi=8.10.0+0.7.0``
    ``python3 -m pip install --user pygments==2.5.2 dominate==2.4.0``

The core library only depends on ``coq-serapi``.  ``dominate`` is used is ``alectryon.html`` to generate HTML output, and ``pygments`` is used by the command-line application for syntax highlighting.

Usage
=====

As a standalone program
-----------------------

``python3 alectryon.py [-h] [--writer {json,html,webpage}] input [input ...]``

- Each ``input`` file can be ``.v`` (a Coq source file, which Alectryon will split into fragments delimited by one or more blank lines) or ``.json`` (a list of Coq fragments).  Each fragment is split into individual sentences, which are executed one by one (all code is run in a single Coq session).

- One output file is written per input file:

  * With ``--writer webpage``, output is written to ``<input>.html`` as a standalone webpage.  This is useful for debugging and to get a quick sense of how Alectryon works.
  * With ``--writer html``, output is written to ``<input>.snippets.html`` as a sequence of ``<pre class="alectryon-io">`` blocks, separated by ``<!-- alectryon-block-end -->`` markers (there will be as many blocks as entries in the input list if ``input`` is a ``.json`` file).
  * With ``--writer json``, output is written to ``<input>.io.json`` as a JSON-encoded list of Coq fragments (as many as in ``input`` if ``input`` is a ``.json`` file).  Each fragment is a list of records, each with a ``_type`` and some type-specific fields.  here is an example:

    Input (``minimal.json``):
        .. code:: json

           ["Example xyz (H: False): True. (* ... *) exact I. Qed.",
            "Print xyz."]

    Output (``minimal.json.io.json``) after running ``./alectryon.py --writer json minimal.json``:
        .. code:: js

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

As a library
------------

Use ``alectryon.annotate(chunks: List[str])``, which returns an object with the same structure as the JSON above, but using objects instead of records with a ``_type`` field:

.. code:: python

    >>> from alectryon import annotate
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

The results of ``annotate`` can be fed to ``alectryon.html.HtmlWriter(highlighter)`` to generate HTML (with CSS classes defined in ``alectryon.css``).  Pass ``highlighter=alectryon.pygments.highlight`` to use Pygments, or any other function from strings to ``dominate`` tags to use a custom syntax highlighter.

As a docutils or Sphinx module
==============================

Add the following code to your Sphinx ``config.py`` file or to your Pelican
setup to register a special ``.. coq::`` directive that feeds its contents to
alectryon and displays the results interleaved with the input::

    import alectryon.docutils
    alectryon.docutils.register()

See |help(docutils)|_ for more information.

To ensure that Coq blocks render properly, you'll need to tell your blogging platform to include ``alectryon.css``.  Using a git submodule or vendoring a copy of Alectryon is an easy way to ensure that this stylesheet is accessible to your blogging software.

By default, Alectryon will raise warnings for lines over 72 characters.  You can change the threshold or silence the warnings by adjusting ``alectryon.docutils.LONG_LINE_THRESHOLD``.  With `Pelican <https://github.com/getpelican/pelican>`_, use the following snippet to make warnings non-fatal::

   DOCUTILS_SETTINGS = {
       'halt_level': 3, # Error
       'warning_stream': None # stderr
   }

.. |help(docutils)| replace:: ``help(alectryon.docutils)``
.. _help(docutils): alectryon/docutils.py

Controlling output
------------------

The ``.. coq::`` directive takes a list of space-separated flags to control the way its contents are displayed:

- One option controls whether output is folded (``fold``) or unfolded (``unfold``).  When output is folded, users can reveal the output corresponding to each input line selectively.

- Multiple options control what is included on each line.
  - ``in``: Include input sentences (``no-in``: hide them)
  - ``goals``: Include goals (``no-goals``: hide them)
  - ``messages``: Include messages (``no-messages``: hide them)
  - ``out``: Include goals and messages (``no-out``: hide them)
  - ``all``: Include input, goals, and messages (``none``: hide them)

The default is ``all fold``, meaning that all output is available, and starts folded.  The exact semantics depend on the polarity of the first inclusion option encountered: ``x y z`` means the same as ``none x y z``, i.e. include ``x``, ``y``, ``z``, and nothing else; ``no-x no-y`` means ``all no-x no-y``, i.e. include everything except ``x`` and ``y``.

These annotations can also be added to individual Coq sentences (⚠ *sentences*, not lines), using special comments of the form ``(* .flag₁ … .flagₙ *)`` (a list of flags each prefixed with a ``.``)::

  .. coq::

     Require Coq.Arith. (* .none *)      ← Executed but hidden
     Goal True. (* .unfold *)            ← Goal unfolded
       Fail exact 1. (* .in .messages *) ← Goal omitted
       Fail fail. (* .messages *)        ← Error message shown, input hidden

Tips
====

Prettification
--------------

Programming fonts with ligatures are a good way to display prettified symbols without resorting to complex hacks.  Good candidates include *Fira Code* and *Iosevka* (with the later, add ``.alectryon-io { font-feature-settings: 'XV00' 1; }`` to your CSS to pick Coq-specific ligatures).

Adding custom keywords
----------------------

You can use ``alectryon.pygments.add_tokens`` to specify additional highlighting
rules, such as custom tactic names.  See |help(add_tokens)|_ for more details.

.. |help(add_tokens)| replace:: ``help(alectryon.pygments.add_tokens)``
.. _help(add_tokens): alectryon/pygments.py

Interactivity
-------------

Alectryon's HTML output doesn't require JavaScript for interactivity, but a separate "slideshow" mode is implemented in ``alectryon-slideshow.js``.
