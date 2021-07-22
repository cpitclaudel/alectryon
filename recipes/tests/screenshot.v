(*|
.. coq:: none
|*)

From Coq Require Import Utf8 ZArith List.
Open Scope Z_scope.
Import ListNotations.

(*|
..
   To compile: alectryon screenshot.v
       # Coq → HTML; produces ‘screenshot.html’

.. raw:: html

   <style type="text/css">
     pre.alectryon-io { font-family: Iosevka; margin: 0pt; }
     .alectryon-standalone .alectryon-windowed { padding: 0.5em; }
     .goal-hyps div:last-child { border: thin solid black; }
     .alectryon-extra-goals label { margin-top: 3px; margin-bottom: 2px; }

     p {
       background: gold;
       /* box-shadow: 2px 2px 3px gray; -- Not in SVG */
       clear: both;
       float: right;
       font-size: 75%;
       font-style: italic;
       line-height: initial;
       margin: 0.1em 0 0 0;
       padding: 0 0.4em 0.1em 0.4em;
       position: relative;
       z-index: 1;
     }

     p::before, p::after {
       display: block;
       content: '';
       position: absolute;
       top: var(--offset-v);
       background: blue;
       left: var(--offset-h);
       right: calc(0pt - var(--offset-h));
       bottom: calc(0pt - var(--offset-v));
       z-index: -1;
     }

     p::before {
       --offset-v: 2px;
       --offset-h: 2px;
       background: goldenrod;
       border: thin solid darkgoldenrod;
     }

     p::after {
       --offset-v: 0px;
       --offset-h: 0px;
       background: gold;
       border: thin solid #333;
     }
   </style>

..
|*)

Goal forall x y, [x + y] = [x - y] -> y = 0. (* .unfold *)

(*|
‘`[=…]`’ is an `injection pattern <https://coq.inria.fr/refman/proof-engine/tactics.html#intro-patterns>`__
|*)

  intros x y [=Heq]. (* .unfold *)
  Search (?u+_ = ?u+_ -> _). (* .unfold .no-goals *)
  apply Z.add_reg_l in Heq. (* .unfold *)

(*|
.. container:: big

   3 cases: `y=0`, `y<0`, `y>0`
|*)

  destruct y; simpl in *.

(*|
`y=0`: trivial
|*)
  1: reflexivity.
(*|
`y!=0`: contradiction in `Heq`
|*)
  all: discriminate.
Qed.
