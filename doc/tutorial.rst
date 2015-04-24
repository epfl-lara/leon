.. _tutorial:

Tutorials
=========

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
`y`, and returns a tuple, which we will here denote `res`.

Note that we use `BigInt` to denote unbounded mathematical
integers. As in Scala and Java, `Int` denotes 32-bit
integers, whereas `BigInt` denotes unbounded integers.

We write `res._1` for the first component of the return
tuple and `res._2` for the second component of the returned
tuple.

The specification says that the set of arguments is equal to
the set consisting of the returned tuple elements. The
notation `Set(x1,x2,...,xN)` denotes a set containing
elements `x1`, `x2`,..., `xN` .

Finally, the `choose` construct takes a variable name (here,
`res`) denoting the value of interest and then gives, after
`=>` a property that this value should satisfy. This
construct allows us to say that we are interested in
computing a result `res` tuple storing the same set as
`{x,y}` but with the first component less then or equal the
second one.  If we view the input as a list of two elements
and the returned tuple as the resulting list of two
elements, we should have performed a very special case of
sorting. Note that the result is uniquely specified.

After invoking Leon on this code (using e.g. http://leon.epfl.ch), we can
choose to synthesize a function corresponding to `choose`.
The system then synthesizes a computation that satisfies
the specification, such as, for, example:

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

Let us now move to defining sorting of any number of elements.
For this purpose, we will define our own lists of `BigInt`.
Note that Leon has a built-in data type of polymorphic lists
(see :ref:`Leon Library <library>`), but here we define our own,
to make the example self-contained (and more tractable for synthesis).

