(*|
To compile::

   alectryon goal-name.v
     # Coq → HTML; produces ‘goal-name.html’
   alectryon goal-name.v -o goal-name.xe.tex --latex-dialect xelatex
     # Coq → LaTeX; produces ‘goal-name.xe.tex’

..
|*)
Goal True -> True /\ True.
  intros; refine (conj ?[G1] ?[G2]). (* .unfold *)
  [G1]: exact I.
  [G2]: exact I.
Qed.
