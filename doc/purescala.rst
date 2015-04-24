.. _purescala:

Pure Scala
==========

The input to Leon is a purely functional **subset** of Scala
(http://www.scala-lang.org/), which we call 
**Pure Scala**. Constructs specific for Leon are defined inside
Leon's libraries in package `leon` and its subpackages. Leon
invokes standard `scalac` compiler on the input file, then
performs additional checks to ensure that the given program
belongs to Pure Scala.

Pure Scala supports two kinds of top-level declarations:

1. Algebraic Data Type (ADT) definitions in the form of an
   abstract class and case classes/objects

.. code-block:: scala

   abstract class MyList
   case object MyEmpty extends MyList
   case class MyCons(elem: BigInt, rest: MyList) extends MyList

2. Objects/modules, for grouping classes and functions

.. code-block:: scala

   object Specs {
      def increment(a: BigInt): BigInt = {
         a + 1
      }

      case class Identifier(id: BigInt)
   }


Algebraic Data Types
--------------------

Abstract Classes
****************

ADT roots need to be defined as abstract, unless the ADT is defined with only one case class/object. Unlike in Scala, abstract classes cannot define fields or constructor arguments.

.. code-block:: scala

 abstract class MyType


Case Classes
************

This abstract root can be extended by a case-class, defining several fields:

.. code-block:: scala

 case class MyCase1(f: Type, f2: MyType) extends MyType
 case class MyCase2(f: Int) extends MyType

.. note::
 You can also define single case-class, for Tuple-like structures.

Case Objects
************

It is also possible to defined case objects, without fields:

.. code-block:: scala

 case object BaseCase extends MyType


Generics
--------

Leon supports type parameters for classes and functions.

.. code-block:: scala

 object Test {
   abstract class List[T]
   case class Cons[T](hd: T, tl: List[T]) extends List[T]
   case class Nil[T]() extends List[T]

   def contains[T](l: List[T], el: T) = { ... }
 }


.. note::
 Type parameters are always **invariant**. It is not possible to define ADTs like:

 .. code-block:: scala

  abstract class List[T]
  case class Cons[T](hd: T, tl: List[T]) extends List[T]
  case object Nil extends List[Nothing]

 Leon in fact restricts type parameters to "simple hierarchies", where subclasses define the same type parameters in the same order.

Methods
-------

You can currently define methods in ADT roots:

.. code-block:: scala

 abstract class List[T] {
   def contains(e: T) = { .. }
 }
 case class Cons[T](hd: T, tl: List[T]) extends List[T]
 case object Nil extends List[Nothing]

 def test(a: List[Int]) = a.contains(42)


Specifications
--------------

Leon supports two kinds of specifications to functions and methods:

Preconditions
*************

Preconditions constraint the argument and is expressed using `require`. It should hold for all calls to the function.

.. code-block:: scala

 def foo(a: Int, b: Int) = {
   require(a > b)
   ...
 }

Postconditions
**************

Postconditions constraint the resulting value, and is expressed using `ensuring`:

.. code-block:: scala

 def foo(a: Int): Int = {
   a + 1
 } ensuring { res => res > a }


Expressions
-----------

Leon supports most purely-functional Scala expressions:

Pattern matching
****************

.. code-block:: scala

 expr match {
    // Simple (nested) patterns:
    case CaseClass( .. , .. , ..) => ...
    case v @ CaseClass( .. , .. , ..) => ...
    case v : CaseClass => ...
    case (t1, t2) => ...
    case 42 => ...
    case _ => ...

    // can also be guarded, e.g.
    case CaseClass(a, b, c) if a > b => ...
 }

Values
******

.. code-block:: scala

 val x = ...

 val (x, y) = ...


Inner Functions
***************

.. code-block:: scala

 def foo(x: Int) = {
   val y = x + 1
   def bar(z: Int) = {
      z + y
   }
   bar(42)
 }


Predefined Types
****************

TupleX
######

.. code-block:: scala

 val x = (1,2,3)
 val x = 1 -> 2 // alternative Scala syntax for Tuple2
 x._1 // 1

Boolean
#######

.. code-block:: scala

  a && b
  a || b
  a == b
  !a

Int
###

.. code-block:: scala

 a + b
 a - b
 -a
 a * b
 a / b
 a % b // a modulo b
 a < b
 a <= b
 a > b
 a >= b
 a == b

.. note::
 Integers are treated as 32bits integers and are subject to overflows.

BigInt
######

.. code-block:: scala

 val a = BigInt(2)
 val b = BigInt(3)

 -a
 a + b
 a - b
 a * b
 a / b
 a % b // a modulo b
 a < b
 a > b
 a <= b
 a >= b
 a == b

.. note::
 BigInt are mathematical integers (arbitrary size, no overflows).

Set
###

.. code-block:: scala

 import leon.lang.Set // Required to have support for Sets

 val s1 = Set(1,2,3,1)
 val s2 = Set[Int]()

 s1 ++ s2 // Set union
 s1 & s2  // Set intersection
 s1 -- s2 // Set difference
 s1 subsetOf s2
 s1 contains 42


Functional Array
################

.. code-block:: scala

 val a = Array(1,2,3)

 a(index)
 a.updated(index, value)
 a.length


Map
###

.. code-block:: scala

 import leon.lang.Map // Required to have support for Maps

 val  m = Map[Int, Boolean](42 -> false)

 m(index)
 m isDefinedAt index
 m contains index
 m.updated(index, value)


Symbolic Input-Output examples
------------------------------

Sometimes, a complete formal specification is hard to write,
especially when it comes to simple, elementary functions. In such cases,
it may be easier to provide a set of IO-examples. On the other hand,
IO-examples can never cover all the possible executions of a function,
and are thus weaker than a formal specification. 

Leon provides a powerful compromise between these two extremes.
It introduces *symbolic IO-examples*, expressed through a specialized ``passes``
construct, which resembles pattern-matching:

.. code-block:: scala

  sealed abstract class List {
    
    def size: Int = (this match {
      case Nil() => 0
      case Cons(h, t) => 1 + t.size
    }) ensuring { res => (this, res) passes {
      case Nil() => 0
      case Cons(_, Nil()) => 1
      case Cons(_, Cons(_, Nil())) => 2
    }}
  }
  case class Cons[T](h: T, t: List[T]) extends List[T]
  case class Nil[T]() extends List[T]


In the above example, the programmer has chosen to partially specify ``size``
through a list of IO-examples, describing what the function should do 
for lists of size 0, 1 or 2.
Notice that the examples are symbolic, in that the elements of the lists are
left unconstrained.

The semantics of ``passes`` is the following.
Let ``a: A`` be a tuple of method parameters and/or ``this``, ``b: B``,
and for each i ``pi: A`` and ``ei: B``. Then

.. code-block:: scala

  (a, b) passes {
    case p1 => e1
    case p2 => e2
    ...
    case pN => eN
  }

is equivalent to

.. code-block:: scala

  a match {
    case p1 => b == e1
    case p2 => b == e2
    ...
    case pN => b == eN
    case _  => true
  }
