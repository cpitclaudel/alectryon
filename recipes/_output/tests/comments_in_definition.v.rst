=========================
 Comments in definitions
=========================

To compile::

   $ alectryon comments_in_definition.v
       # Coq → HTML; produces ‘comments_in_definition.html’

   $ alectryon comments_in_definition.v --backend rst
       # Coq → reST; produces ‘comments_in_definition.v.rst’

Some Alectryon drivers support mixing prose directly *inside* definitions, not just *between* them.

.. note::

   Mixing literate comments into definitions can be confusing when working in an indentation-sensitive language like Markdown or reST.  Keep in mind that alectryon strips all spaces directly following|preceding a literate comment opener|closer, so a literate comment on its own line will always end up starting at column 0.

   If you're not sure of how Alectryon sees your file after processing comments, convert it to `.rst` to check.

.. coq::

   Module Example1.
     Inductive Nat :=

`0` is written as `O`

.. coq::

     | O

`1 + n` is written as `Succ n`

.. coq::

     | Succ

Notice that the `n` is written as an argument to Succ:

.. coq::

         (n: Nat)

The return type is `Nat`

.. coq::

       : Nat.

This also works with definitions:

.. coq::

     Definition is_zero (n: Nat): bool :=
       match n with
       | O =>

Base case…

.. coq::

           true
       | Succ _ =>

… and another base case

.. coq::

           false
       end.
   End Example1.

Internally, Alectryon sees this example in just the same way as the following one:

.. coq::

   Module Example2.
     Inductive Nat :=

`0` is written as `O`

.. coq::

     | O

`1 + n` is written as `Succ n`

.. coq::

     | Succ

Notice that the `n` is written as an argument to Succ:

.. coq::

         (n: Nat)

The return type is `Nat`

.. coq::

       : Nat.

This also works with definitions:

.. coq::

     Definition is_zero (n: Nat): bool :=
       match n with
       | O =>

Base case…

.. coq::

           true
       | Succ _ =>

… and another base case

.. coq::

           false
       end.
   End Example2.
