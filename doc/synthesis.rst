.. _synthesis:

Synthesis
=========

Software synthesis offers an alternative way of developing trustworthy
programs. At a high level, program specifications describe **what** the
function should do, and its corresponding implementation describes **how** it
will do it. While verification ensures that both views match, synthesis
consists of translating these specifications (or expectations) to executable
programs which realises them.

As we have seen previously, relatively precise specifications of complex
operations can be written consicely. Synthesis can thus reduce development time
and allows the user to focus on high-level aspects.

Deductive Synthesis Framework
-----------------------------

Closing Rules
-------------

Optimistic Ground
^^^^^^^^^^^^^^^^^

CEGIS
^^^^^

TEGIS
^^^^^

Ground
^^^^^^

Decomposing Rules
-----------------

Equality Split
^^^^^^^^^^^^^^

Given two input variables `a` and `b` of compatible types, this rule
considers the cases where `a = b` and `a != b`. From:

.. code-block:: scala

  choose(res => spec(a, b, res))


this rule generates two sub-chooses, and combines them as follows:

.. code-block:: scala

   if (a == b) {
     choose(res => spec(a, a, res))
   } else {
     choose(res => spec(a, b, res))
   }


Inequality Split
^^^^^^^^^^^^^^^^

Given two input variables `a` and `b` of numeric type, this rule
considers the cases where `a < b`, `a == b`, and `a > b`. From:

.. code-block:: scala

  choose(res => spec(a, b, res))


this rule generates three sub-chooses, and combines them as follows:

.. code-block:: scala

   if (a < b) {
     choose(res => spec(a, b, res))
   } else if (a > b) {
     choose(res => spec(a, b, res))
   } else {
     choose(res => spec(a, a, res))
   }


ADT Split
^^^^^^^^^

Given a variable `a` typed as an algebraic data type `T`, the rules decomposes
the problem in cases where each case correspond to one subtype of `T`:

.. code-block:: scala

  abstract class T
  case class A(f1: Int) extends T
  case class B(f2: Boolean) extends T
  case object C extends T

  choose(res => spec(a, res))


this rule generates three sub-chooses, in which the input variable `a` is
substituted by the appropriate case, and combines them as follows:

.. code-block:: scala

   a match {
     case A(f1) => choose(res => spec(A(f1), res))
     case B(f2) => choose(res => spec(B(f2), res))
     case C     => choose(res => spec(C, res))
   }


Int Induction
^^^^^^^^^^^^^

Given an integer (or bigint) variable `a`, the rules performs induction on `a`:

.. code-block:: scala

  choose(res => spec(a, res))


this rule generates three sub-chooses, one for the base case and one for each inductive case (we allow negative numbers):

.. code-block:: scala

   def tmp1(a: Int) = {
     if (a == 0) {
       choose(res => spec(a, res))
     } else if (a > 0) {
       val r1 = tmp1(a-1)
       choose(res => spec(a, res))
     } else if (a < 0) {
       val r1 = tmp1(a+1)
       choose(res => spec(a, res))
     }
   }

   tmp1(a)

This allows Leon to synthesize a well-structured recursive function.

One Point
^^^^^^^^^

This syntactic rule considers equalities of a variable at the top level of the
specification, and substitutes the variable with the corresponding expression in
the rest of the formula. Given the following specification:

.. math::
    a = expr \land \phi
  
and assuming :math:`expr` does not use :math:`a`, we generate the alternative and
arguable simpler specification:


.. math::
    \phi[a \rightarrow expr]

This rule is typically combined with `Unused Input` or `Unconstrained Output` to
actually eliminate the input or output variable form the synthesis problem.

Assert
^^^^^^

The `Assert` rule scans the specification for predicates that only constraint
input variables and lifts them out of the specification. Since these are
constraints over the input variables, they typically represent the
precondition necessary for the ``choose`` to be feasible.
Given an input variable `a`:

.. code-block:: scala

  choose(res => spec(a, res) && pred(a))

will become:

.. code-block:: scala

  require(pred(a))

  choose(res => spec(a, res))

Case Split
^^^^^^^^^^

This rule considers a top-level disjunction and decomposes it:

.. code-block:: scala

  choose(res => spec1(a, res) || spec2(a, res))

thus becomes two sub-chooses

.. code-block:: scala

  if (P) {
    choose(res => spec1(a, res))
  } else {
    choose(res => spec2(a, res))
  }

Here we note that ``P`` is not known until the first ``choose`` is solved, as it
corresponds to its precondition.



Equivalent Input
^^^^^^^^^^^^^^^^

This rule discovers equivalences in the input variables in order to eliminate
redundancies. We consider two kinds of equivalences:

 1) Simple equivalences: the specification contains  :math:`a = b` at the top
 level.
Equivawhetherlent input takes a synthesis problem with two compatible input variables
`a` and `b` relies on an SMT solver to establish if the path-condition implies
that `a == b`

Unused Input
^^^^^^^^^^^^

Unconstrained Output
^^^^^^^^^^^^^^^^^^^^


..
    Unification.DecompTrivialClash,
    Disunification.Decomp,
    ADTDual,
    CaseSplit,
    IfSplit,
    DetupleOutput,
    DetupleInput,
    InnerCaseSplit
