.. _tutorial:

Tutorials
=========

Sorting Lists
-------------

This tutorial shows how to define lists as algebraic data
types, how to **verify** certain properties of an insertion
sort, as well as how to use Leon to **synthesize**
operations from specifications.

Defining lists
^^^^^^^^^^^^^^

Leon has a built-in data type of polymorphic lists (see 

Let us start by specifying a function that sorts **two**
mathematical integers.

.. code-block:: scala

  import leon.lang._
  import leon.lang.synthesis._
  object Sort {
    def sort2(x : BigInt, y : BigInt) = choose{(res: (BigInt,BigInt)) =>
      Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
    }
  }

