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

Ground
^^^^^^

This rule applies when the synthesis problem has no input variables. If the
specification is satisfiable, its model corresponds to a valid solution. We
rely on SMT solvers to check satisfiability of the formulas. For instance:

.. code-block:: scala

  choose ((x: Int, y: Int) => x > 42 && y > x)

can trivially be synthesized by ``(1000, 1001)``.

If the specification turns out to be UNSAT, the synthesis problem is impossible
and we synthesize it as an ``error`` with a ``false`` precondition.


Optimistic Ground
^^^^^^^^^^^^^^^^^

This rule acts like `Ground`, but without the requirement on the absence of input
variables. The reasonning is that even though the problem has input variables,
the solutions might still be a constant expression.

`Optimistic Ground` also tries to satisfy the specification, but it also needs
to validate the resulting model. That is, given a valuation of output
variables, it checks whether it exists a valuation for input variables such that
the specification is violated. The model is discarded if such counter-example
is found. If no counter-example exist, we solve the synthesis problem with the
corresponding values.

The rule tries at most three times to discover a valid value.

CEGIS
^^^^^

TEGIS
^^^^^

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

This syntactic rule considers equalities of an output variable at the top level of the
specification, and substitutes the variable with the corresponding expression in
the rest of the formula. Given the following specification:

.. math::
    res1 = expr \land \phi
  
and assuming :math:`expr` does not use :math:`a`, we generate the alternative and
arguable simpler specification:


.. math::
    \phi[res1 \rightarrow expr]


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

 2) ADT equialences: the specification contains :math:`l.isInstanceOf[Cons]
 \land h = l.head \land t = l.tail` which entails :math:`l = Cons(h, t)` and
 thus allows us to substitute :math:`l` by :math:`Cons(h, t)`.

Eliminating equivalences prevents explosion of redundant rule instanciations.
For instance, if you have four integer variables where three of them are
equivalent, Leon has 6 ways of applying `Inequality Split`. After
eliminating equivalences, only one application remains posible.

Unused Input
^^^^^^^^^^^^

This rule tracks input variables (variables originally in scope of the
``choose``) that are not constrained by the specification or the
path-condition. These input variables carry no information and are thus
basically useless. The rule consequently eliminates them from the set of input
variables with which rules may be instantiated.

Unconstrained Output
^^^^^^^^^^^^^^^^^^^^

This rule is the dual of ``Unused Input``: it tracks output variable (result
values) that are not constrained. Such variables can be trivially synthesized
by any value or expression of the right type. For instance: 

.. code-block:: scala

  choose ((x: Int, y: T) => spec(y))

becomes

.. code-block:: scala

  (0, choose ((y: T) => spec(y)))

Leon will use the simplest value of the given type, when available. Note this
rule is not able to synthesize variables of generic types, as no literal values
exist for these. While ``null`` may be appropriate in Scala, Leon does not
define it.

..
    Unification.DecompTrivialClash,
    Disunification.Decomp,
    ADTDual,
    CaseSplit,
    IfSplit,
    DetupleOutput,
    DetupleInput,
    InnerCaseSplit
