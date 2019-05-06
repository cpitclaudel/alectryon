===========
 Alectryon
===========

Annotate Coq source files, showing goals and messages for each Coq sentence.

Setup
=====

Dependencies (OCaml, Python 3):
    ``opam install coq-serapi=8.9.0+0.6.0``
    ``pip3 install --user pexpect==4.7.0 pygments==2.3.1 dominate==2.3.5 sexpdata==0.0.3``

Usage
=====

As a standalone program
-----------------------

``python3 alectryon.py [-h] [--writer {json,html,webpage}] input [input ...]``

- Each ``input`` file can be ``.v`` (a Coq source file) or ``.json`` (a list of Coq fragments).  All code is run in a single Coq session.

- One output file is written per input file:

  * With ``--writer webpage``, output is written to ``<input>.html`` as a standalone webpage.  This is useful for debugging and to get a quick sense of how Alectryon works.
  * With ``--writer html``, output is written to ``<input>.snippets.html`` as a sequence of ``<pre class="alectryon-io">`` blocks, separated by ``<!-- alectryon-block-end -->`` markers (there will be only one block if ``input`` is a ``.v`` file, and as many blocks as entries in the input list if ``input`` is a ``.json`` file).
  * With ``--writer json``, output is written to ``<input>.io.json`` as a JSON-encoded list of Coq fragments (only on if ``input`` is a ``.v`` file, and as many as in ``input`` if ``input`` is a ``.json`` file).  Each fragment is a list of records, each with a ``_type`` and some type-specific fields.  here is an example:

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
