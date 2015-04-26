.. _tutorial:

Tutorial: Sorting
=================

This tutorial shows how to:

  * use the `choose` construct for synthesis and constraint solving
  * define lists as algebraic data types
  * use sets to specify properties of interest
  * specify sortedness of a list and use function contracts
  * verify properties of an insertion into a sorted list
  * execute or synthesize provably correct operations using specifications alone,
    without the need to write implementation

For this tutorial we occasionally assume that the user is using the web 
interface. The functionality is also available (possibly with less
convenient interface) from the command line, see :ref:`gettingstarted`.

Sorting Two Elements
--------------------

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Leon contains a built-in evaluator. To see it in action in
the web interface, just define a function without
parameters, such as 

.. code-block:: scala

    def test1 = sort2(30, 4)

Hovering over `test1` should display the computed result
`(4,30)`. From :ref:`cmdlineoptions`, use `--eval`.

This shows that Leon's evaluator can also execute `choose`
constructs. In other words, it supports programming
with constraints. Executing the `choose` construct
is, however, expensive. Moreover, the execution times
are not very predictable. This is why it is desirable
to eventually replace your `choose` constructs with
more efficient code. Leon can automate this process
in some cases, using **synthesis**.

Synthesizing Sort for Two Elements
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
of the program output is unambiguous, so all programs that
one can synthesize compute the same results for all inputs.

Remarks on Uniqueness
^^^^^^^^^^^^^^^^^^^^^

Let us give a name to the specification for `sort2`.

.. code-block:: scala

  def sort2spec(x: BigInt, y: BigInt, res: (BigInt, BigInt)): Boolean = {
    Set(x,y) == Set(res._1, res._2) && res._1 <= res._2
  }

We can then prove that the result is unique, by asking Leon
to show the following function returns `true` for all inputs
for which the `require` clause holds.

.. code-block:: scala

  def unique2(x: BigInt, y: BigInt, 
            res1: (BigInt, BigInt),
            res2: (BigInt, BigInt)): Boolean = {
    require(sort2spec(x,y,res1) && sort2spec(x,y,res2))
    res1 == res2
  }.holds

In contrast, if we define the corresponding specification for three integers

.. code-block:: scala

  def sort3spec(x: BigInt, y: BigInt, z: BigInt, res: (BigInt, BigInt, BigInt)): Boolean = {
    Set(x,y,z) == Set(res._1, res._2, res._3) && res._1 <= res._2 && res._2 <= res._3
  }

Then uniqueness of the solution is the following conjecture:

.. code-block:: scala
  
  def unique3(x: BigInt, y: BigInt, z: BigInt, 
      res1: (BigInt, BigInt, BigInt),
      res2: (BigInt, BigInt, BigInt)): Boolean = {
    require(sort3spec(x,y,z,res1) && sort3spec(x,y,z,res2))
    res1 == res2
  }.holds

This time, however, Leon will report a counterexample, indicating
that the conjecture does not hold. One such counterexample is
0, 1, 1, for which the result (0, 0, 1) also satisfies the specification,
because sets ignore the duplicates, so 

.. code-block:: scala

    Set(x,y,z) == Set(res._1, res._2, res._2)

is true. This shows that writing specifications can be subtle, but Leon's
capabilities can help in the process as well.

Defining Lists and Their Properties
-----------------------------------

We next consider sorting an unbounded number of elements.
For this purpose, we define a data structure for lists of
integers.  Leon has a built-in data type of parametric
lists, see :ref:`Leon Library <library>`, but here we define
our own variant instead. 

Lists
^^^^^

We use a recursive algebraic data type
definition, expressed using Scala's **case classes**.

.. code-block:: scala

  sealed abstract class List
  case object Nil extends List
  case class Cons(head: BigInt, tail: List) extends List

We can read the definition as follows: the set of lists is
defined as the least set that satisfies them:

  * empty list `Nil` is a list
  * if `head` is an integer and `tail` is a `List`, then
    `Cons(head,tail)` is a `List`.

Each list is constructed by applying the above two rules
finitely many times.  A concrete list containing elements 5,
2, and 7, in that order, is denoted

.. code-block:: scala

    Cons(5, Cons(2, Cons(7, Nil)))

Having defined the structure of lists, we can move on to
define some semantic properties of lists that are of
interests. For this purpose, we use recursive functions
defined on lists. 

Size of a List
^^^^^^^^^^^^^^

As the starting point, we define size of a list.

.. code-block:: scala

    def size(l: List) : BigInt = (l match {
        case Nil => 0
        case Cons(x, rest) => 1 + size(rest)
    })

We can add a specification that the size is non-negative.

.. code-block:: scala

    def size(l: List) : BigInt = (l match {
        case Nil => 0
        case Cons(x, rest) => 1 + size(rest)
    }) ensuring(res => res >= 0)

The construct `ensuring(res => P)` denotes that, if
we denote by `res` the return value of the function,
then `res` satisfies the boolean-valued expression `P`.
We call the predicate `P` the **postcondition**.

Sorted Lists
^^^^^^^^^^^^

We define properties of values simply as executable
predicates that check if the property holds. The following
is a property that a list is sorted in a strictly ascending
order.

.. code-block:: scala

    def isSorted(l : List) : Boolean = l match {
      case Nil => true
      case Cons(_,Nil) => true
      case Cons(x1, Cons(x2, rest)) => 
        x1 < x2 && isSorted(Cons(x2,rest))
    }

Insertion into Sorted List
--------------------------

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => isSorted(res)}

Being Sorted is Not Enough
--------------------------

A function such as this one is correct.

.. code-block:: scala

    def fsInsert(x : BigInt, l : List) : List = {
      require(isSorted(l))
      Nil
    } ensuring {(res:List) => isSorted(res)}

So, our specification may be considered weak.

Using Size in Specification
---------------------------

Consider a stronger additional postcondition property:

.. code-block:: scala

  size(res) == size(l) + 1

Does it hold? If we try to add it, we obtain a counterexample.
A correct strengthening, taking into account that the element
may or may not already be in the list, is:

.. code-block:: scala

  size(l) <= size(res) && size(res) <= size(l) + 1

Using Content in Specification
------------------------------

A stronger specification needs to talk about the `content`
of the list.

.. code-block:: scala

  def sInsert(x : BigInt, l : List) : List = {
    require(isSorted(l))
    l match {
      case Nil => Cons(x, Nil)
      case Cons(e, rest) if (x == e) => l
      case Cons(e, rest) if (x < e) => Cons(x, Cons(e,rest))
      case Cons(e, rest) if (x > e) => Cons(e, sInsert(x,rest))
    }
  } ensuring {(res:List) => 
     isSorted(res) && content(res) == content(l) ++ Set(x)}

To compute content, in this example we use sets, even though
it might be better in general to use multisets.

.. code-block:: scala

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }


Sorting Specification and Running It
------------------------------------

.. code-block:: scala

  def sortMagic(l : List) = choose{(res:List) => 
    isSorted(res) && content(res) == content(l)
  }

We can execute it.

.. code-block:: scala

  def mm = sortMagic(Cons(20, Cons(5, Cons(50, Cons(2, Nil)))))

obtaining the expected `Cons(2, Cons(5, Cons(20, Cons(50, Nil))))`.


Synthesizing Sort
-----------------

By asking the system to synthesize the `choose` construct,
we may obtain a function such as the following, which gives
us the natural insertion sort.

.. code-block:: scala

    def sortMagic(l : List): List = {
      l match {
        case Cons(head, tail) =>
          sInsert(head, sortMagic(tail))
        case Nil => Nil
      }
    }

Going back and Synthesizing Insertion
-------------------------------------

In fact, if we had a precise enough specification of insert,
we could have synthesized it from the specification.

.. code-block:: scala

  def insertMagic(x: BigInt, l: List): List = {
    require(isSorted(l))
    choose {(res: List) => 
      isSorted(res) && content(res) == content(l) ++ Set[BigInt](x)
    }
  }

