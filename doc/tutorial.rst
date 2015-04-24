.. _tutorial:

Tutorials
=========

For these tutorials we occasionally assume that the user is using the web 
interface. The functionality is also available (possibly with less
convenient interface) from the command line, see :ref:`gettingstarted`.

Sorting Lists
-------------

This tutorial shows how to define lists as algebraic data
types, how to **verify** certain properties of an insertion
sort. We finish showing how to use Leon to **synthesize**
provably correct operations from specifications.

A Preview of Specification and Synthesis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As a preview, let us start by **specifying** a function that
sorts **two** mathematical integers. Here is what we need
to write.

.. code-block:: scala

  import leon.lang._
  import leon.lang.synthesis._
  object Sort {
    def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
      Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
    }
  }

A Leon program consists of one or more modules delimited by
`object` and `class` declarations. We use `import` to
include core constructs that are specific to Leon. Note
that, with the definitions in `leon._` packages, Leon
programs should also compile with the standard Scala
compiler. In that sense, Leon is a proper subset of Scala.

Our initial function that "sorts" two mathematical integers
is named `sort2`.  Namely, it accepts two arguments, `x` and
`y`, and returns a tuple, which we will here denote `res`,
which stores either `(x,y)` or `(y,x)` such that the first
component is less than equal the second component.

Note that we use `BigInt` to denote unbounded mathematical
integers. As in Scala and Java, `Int` denotes 32-bit
integers with the usual signed arithmetic operations from
computer architecture. In contrast, `BigInt` denotes the
unbounded integers, which closely mimic mathematical
integers.

As usual in Scala, we write `res._1` for the first component
of the return tuple `res`, and `res._2` for the second
component of the tuple.

The specification says that the set of arguments is equal to
the set consisting of the returned tuple elements. The
notation `Set(x1,x2,...,xN)` denotes

.. math::

  \{ x_1, \ldots, x_N \}

that is, a finite set containing precisely the elements 
`x1`, `x2`,..., `xN`.

Finally, the `choose` construct takes a variable name (here,
`res`) denoting the value of interest and then gives, after
the `=>` symbol, a property that this value should
satisfy. We can read `choose{(x:T) => P}` as 

**choose x of type T such that P**

Here, we are interested in computing a result `res` tuple
such that the set of elements in the tuple is the same as
`{x,y}` and that the elements are in ascending order in the
tuple.  The specification thus describes sorting of lists of
length two.  Note that the result is uniquely specified, no
matter what the values of `x` and `y` are.

Evaluating exppressions containing choose
.........................................

Leon contains a built-in evaluator. To see it in action in
the web interface, just define a function without
parameters, such as 

.. code-block:: scala

    def test1 = sort2(30, 4)

Hovering over the definition of test1 should display
the computed tuple `(4,30)`.

This shows that Leon's evaluator can also execute `choose`
constructs. In other words, it supports programming
with constraints. Executing the `choose` construct
is, however, expensive. Moreover, the execution times
are not very predictable. This is why it is desirable
to eventually replace your `choose` constructs with
more efficient code. Leon can automate this process
in some cases, using **synthesis**.

Synthesizing the sort of two elements
.....................................

Instead of executing `choose` using a constraint solver
during execution, we can alternatively instruct Leon to
synthesize a function corresponding to `choose`.  The system
then synthesizes a computation that satisfies the
specification, such as, for, example:

.. code-block:: scala

    def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
      if (x < y) x
      else y
    }

Depending on the particular run, Leon may also produce a solution such as

.. code-block:: scala

  def sort2(x : BigInt, y : BigInt): (BigInt, BigInt) = {
    if (x < y) {
      (x, y)
    } else if (x == y) {
      (x, x)
    } else {
      (y, x)
    }
  }

This code performs some unnecessary case analysis, but still
satisfies our specification. In this case, the specification
is unambiguous, so all programs that one can synthesize
compute the same results for all inputs.

Defining lists
^^^^^^^^^^^^^^

Let us now consider sorting of any number of elements.

For this purpose, we define the data structure of lists of
(big) integers.  (Leon has a built-in data type of
polymorphic lists, see :ref:`Leon Library <library>`, but
here we will define our own variant.)

