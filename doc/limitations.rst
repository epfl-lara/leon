.. _limitations:

Limitations of Verification
---------------------------

A goal of Leon is to ensure that proven properties hold in
all program executions so that, for example, verified programs
do not crash and all of the preconditions and postconditions
are true in all executions.
For this to be the case, there needs
to be a precise correspondence between runtime execution
semantics and the semantics used in verification, including
the SMT solvers invoked. 

Below we document several cases where we are aware that the
discrepancy exists and provide suggested workarounds.

Integer Division and Modulo
^^^^^^^^^^^^^^^^^^^^^^^^^^^

On `BigInt` data types, the division operator `/` and
the modulo operator `%` should only be invoked with positive
arguments. There are several specific issues.

First, Leon currently does not check for division by zero.
You can work around this by defining your own division operator
with the corresponding precondition.

Second, division has rounding-to-zero runtime semantics,
following Java Virtual Machine and the `BigInt` library
of Java and Scala, so `(-14)/3 == -4` and, more generally,
`(-x)/y = -(x/y)`. In general, modulo operator `%` is defined
so it can be used together with `/`, so that 
`(x/y)*y + (x % y) == x`. Thus, `(-14) % 3 == -2`.

In contrast, SMT solvers following the SMT-LIB standard use
rounding to negative infinity, so `(-14)/3 == -5` is a
theorem, and `(-14) % 3 == 1`. With SMT-LIB semantics, the
result of modulo `x % y` is non-negative and less than the
absolute value of `y`.

For the moment we therefore recommend defining your own
operators with appropriate preconditions. Note that the
capabilities for automated proofs are limited when the
second argument of `/` or `%` is not a constant literal.

Out of Memory Errors
^^^^^^^^^^^^^^^^^^^^

By default Leon assumes that unbounded data types can
be arbitrarily large and that all well-founded recursive
functions have enough stack space to finish their computation.
Thus a verified program may crash at run-time due to:
  * stack overflow
  * heap overflow

Algebraic data types are assumed to be arbitrarily large.
In any given execution, there will be actual bounds on the
total available memory, so the program could crash with out
of memory error when trying to allocate another value of
algebraic data type. 

For a safety critical application you may wish to resort to
tail-recursive programs only, and also write preconditions
and postconditions that enforce a bound on the maximum size
of the data structures that your application
manipulates. For this purpose, you can define size functions
that return `BigInt` data types.

