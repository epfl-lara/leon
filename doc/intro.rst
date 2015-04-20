Introduction
============

The Leon system is an automated system for verifying, repairing, and
synthesizing Scala programs.

Leon supports programs written in :ref:`Pure Scala <purescala>`, a purely
functional subset of Scala.  The :ref:`XLang <xlang>` extension enables Leon to
work on a richer subset of Scala, including imperative features. From the
perspective of the end user, that distinction between the two sets of features
should be mostly meaningless, but it can help getting an intuition when trying
to prove difficult properties.

The :ref:`Pure Scala <purescala>` features are at the *core* of the Leon
system. They are considered as primitives and get a personalized treatment in
the solving algorithms of Leon. On the other hand, any feature introduced by
:ref:`XLang <xlang>` can be --- and is --- encoded into a mix of Pure Scala
concepts. However, they are more than just syntactic sugar --- some of those
features actually require significant modification of the original program.

Software Verification
---------------------

Leon started out as a program verifier for :ref:`Pure Scala <purescala>`. It
would collect a list of top level functions written in Pure Scala, and verifies
the *validity* of their *contracts*. Essentially, for each function, 
it would prove that the postcondition always hold, assuming a given precondition does
hold. A simple example:

.. code-block:: scala

   def factorial(n: Int): Int = {
     require(n >= 0)
     if(n == 0) {
       1
     } else {
       n * factorial(n - 1)
     }
   } ensuring(res => res >= 0)

Leon generates a ``postcondition`` verification condition for the above
function, corresponding to the predicate parameter to the ``ensuring``
expression. It attempts to prove it using a combination of an internal
algorithm and external automated theorem proving. Leon will return one of the
following:

* The postcondition is ``valid``. In that case, Leon was able to prove that for **any**
  input to the function satisfiying the precondition, the postcondition will always hold.
* The postcondition is ``invalid``. It means that Leon disproved the postcondition and
  that there exists at least one input satisfying the precondition and such that the
  postcondition does not hold. Leon will always return a concrete counterexample, very
  useful when trying to understand why a function is not satisfying its contract.
* The postcondition is ``unknown``. It means Leon is unable to prove or find a counterexample.
  It usually happens after a timeout or an internal error occuring in the external 
  theorem prover. 

Leon will also verify for each call site that the precondition of the invoked
function cannot be violated.

Leon supports verification of a significant part of the Scala language, described in the
sections :ref:`Pure Scala <purescala>` and :ref:`XLang <xlang>`.




Program Synthesis
-----------------


Program Repair
--------------
