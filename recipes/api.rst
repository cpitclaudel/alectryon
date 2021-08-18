===========
 API Usage
===========

This file demonstrates a few uses of Alectryon's Python APIs.

   >>> import sys; from pathlib import Path; from pprint import pprint
   >>> recipes = Path(".").absolute()
   >>> libdir = recipes / "src"

To compile::

   $ python -m doctest -v -o NORMALIZE_WHITESPACE api.rst > api.rst.out
      # run Doctests; produces ‘api.rst.out’

Annotating Coq snippets
=======================

Use ``alectryon.core.annotate`` to transform a process a list of fragments of statements using SerAPI:

   >>> from alectryon.core import annotate
   >>> annotate(["Check surjective_pairing."])
   [[Sentence(contents='Check surjective_pairing.',
              messages=[Message(contents='surjective_pairing\n
                : forall (A B : Type) (p : A * B),\n
                   p = (fst p, snd p)')],
                                goals=[])]]

Here is a larger example:

   >>> fragments = ["Check 1.", "Goal False -> True. intros H."]
   >>> sertop_args = ("-Q", "{},lib".format(libdir))
   >>> annotated = annotate(fragments, sertop_args=sertop_args)
   >>> pprint(annotated, width=65)
   [[Sentence(contents='Check 1.',
              messages=[Message(contents='1\n     : nat')],
              goals=[])],
    [Sentence(contents='Goal False -> True.',
              messages=[],
              goals=[Goal(name=None,
                          conclusion='False -> True',
                          hypotheses=[])]),
     Text(contents=' '),
     Sentence(contents='intros H.',
              messages=[],
              goals=[Goal(name=None, conclusion='True',
                          hypotheses=[Hypothesis(names=['H'],
                                                 body=None,
                                                 type='False')])])]]

Serializing
===========

These results can be serialized to JSON:

   >>> from alectryon.json import PlainSerializer
   >>> encoded = PlainSerializer.encode(annotated)
   >>> pprint(encoded, width=65)
   [[{'_type': 'sentence',
      'contents': 'Check 1.',
      'goals': [],
      'messages': [{'_type': 'message',
                    'contents': '1\n     : nat'}]}],
    [{'_type': 'sentence',
      'contents': 'Goal False -> True.',
      'goals': [{'_type': 'goal',
                 'conclusion': 'False -> True',
                 'hypotheses': [],
                 'name': None}],
      'messages': []},
     {'_type': 'text', 'contents': ' '},
     {'_type': 'sentence',
      'contents': 'intros H.',
      'goals': [{'_type': 'goal',
                 'conclusion': 'True',
                 'hypotheses': [{'_type': 'hypothesis',
                                 'body': None,
                                 'names': ['H'],
                                 'type': 'False'}],
                 'name': None}],
       'messages': []}]]

Use ``json.dump`` to save them to a stream:

   >>> import json
   >>> js = json.dumps(encoded)
   >>> js[:72]
   '[[{"_type": "sentence", "contents": "Check 1.", "messages": [{"_type": "'

Exporting
=========

The resulting JSON can be turned back into a movie:

   >>> encoded = json.loads(js)
   >>> annotated = PlainSerializer.decode(encoded)

And that movie can be exported to LaTeX or HTML:

   >>> from alectryon.html import HtmlGenerator
   >>> from alectryon.pygments import make_highlighter
   >>> for dom in HtmlGenerator(make_highlighter("html")).gen(annotated):
   ...     print(dom)
   <pre class="alectryon-io highlight"><!-- Generator: Alectryon --><span class="alectryon-sentence"><input class="alectryon-toggle" id="chk0" style="display: none" type="checkbox"><label class="alectryon-input" for="chk0"><span class="kn">Check</span> <span class="mi">1</span>.</label><small class="alectryon-output"><div><div class="alectryon-messages"><blockquote class="alectryon-message"><span class="mi">1</span>
        : nat</blockquote></div></div></small></span></pre>
   <pre class="alectryon-io highlight"><!-- Generator: Alectryon --><span class="alectryon-sentence"><input class="alectryon-toggle" id="chk1" style="display: none" type="checkbox"><label class="alectryon-input" for="chk1"><span class="kn">Goal</span> <span class="kt">False</span> -&gt; <span class="kt">True</span>.</label><small class="alectryon-output"><div><div class="alectryon-goals"><blockquote class="alectryon-goal"><span class="goal-separator"><hr></span><div class="goal-conclusion"><span class="kt">False</span> -&gt; <span class="kt">True</span></div></blockquote></div></div></small><span class="alectryon-wsp"> </span></span><span class="alectryon-sentence"><input class="alectryon-toggle" id="chk2" style="display: none" type="checkbox"><label class="alectryon-input" for="chk2"><span class="nb">intros</span> H.</label><small class="alectryon-output"><div><div class="alectryon-goals"><blockquote class="alectryon-goal"><div class="goal-hyps"><span><var>H</var><span class="hyp-type"><b>: </b><span><span class="kt">False</span></span></span></span><br></div><span class="goal-separator"><hr></span><div class="goal-conclusion"><span class="kt">True</span></div></blockquote></div></div></small></span></pre>

   >>> from alectryon.latex import LatexGenerator
   >>> from alectryon.pygments import make_highlighter
   >>> for ltx in LatexGenerator(make_highlighter("latex")).gen(annotated):
   ...     print(ltx)
   \begin{alectryon}
     % Generator: Alectryon
     \sep
     \begin{sentence}
       \begin{input}
         \PY{k+kn}{Check}~\PY{l+m+mi}{1}\PY{o}{.}
       \end{input}
       \sep
       \begin{output}
         \begin{messages}
           \begin{message}
             \PY{l+m+mi}{1}\nl
             ~~~~~\PY{o}{:}~\PY{n}{nat}
           \end{message}
         \end{messages}
       \end{output}
     \end{sentence}
   \end{alectryon}
   \begin{alectryon}
     % Generator: Alectryon
     \sep
     \begin{sentence}
       \begin{input}
         \PY{k+kn}{Goal}~\PY{k+kt}{False}~\PY{o}{\PYZhy{}\PYZgt{}}~\PY{k+kt}{True}\PY{o}{.}
       \end{input}
       \sep
       \begin{output}
         \begin{goals}
           \begin{goal}
             \begin{hyps}\end{hyps}
             \sep
             \infrule{}
             \sep
             \begin{conclusion}
               \PY{k+kt}{False}~\PY{o}{\PYZhy{}\PYZgt{}}~\PY{k+kt}{True}
             \end{conclusion}
           \end{goal}
         \end{goals}
       \end{output}
     \end{sentence}
     \sep
     \begin{sentence}
       \begin{input}
         \PY{n+nb}{intros}~\PY{n}{H}\PY{o}{.}
       \end{input}
       \sep
       \begin{output}
         \begin{goals}
           \begin{goal}
             \begin{hyps}
               \hyp{H}{\PY{k+kt}{False}}
             \end{hyps}
             \sep
             \infrule{}
             \sep
             \begin{conclusion}
               \PY{k+kt}{True}
             \end{conclusion}
           \end{goal}
         \end{goals}
       \end{output}
     \end{sentence}
   \end{alectryon}

Look at the implementation of ``cli.py`` for more examples.
