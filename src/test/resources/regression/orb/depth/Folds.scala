import leon.instrumentation._
import leon.invariant._


object TreeMaps {

  sealed abstract class Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case class Leaf() extends Tree

  def height(t: Tree): BigInt = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  }

  def parallelSearch(elem : BigInt, t : Tree) : Boolean = {
    t match {
      case Leaf() => false
      case Node(l, x, r) =>
        if(x == elem) true
        else {
          val r1 = parallelSearch(elem, r)
          val r2 = parallelSearch(elem, l)
          if(r1 || r2) true
          else false
        }
    }
  } ensuring(res => true && tmpl((a,b) => depth <= a*height(t) + b))


  def squareMap(t : Tree) : Tree = {
    t match {
      case Leaf() => t
      case Node(l, x, r) =>
        val nl = squareMap(l)
        val nr = squareMap(r)
        Node(nl, x*x, nr)
    }
  } ensuring (res => true && tmpl((a,b) => depth <= a*height(t) + b))

  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  def fact(n : BigInt) : BigInt = {
    require(n >= 0)

    if(n == 1 || n == 0) BigInt(1)
    else n * fact(n-1)

  } ensuring(res => tmpl((a,b) => depth <= a*n + b))

  def descending(l: List, k: BigInt) : Boolean = {
    l match {
      case Nil() => true
      case Cons(x, t) => x > 0 && x <= k && descending(t, x-1)
    }
  }

  def factMap(l: List, k: BigInt): List = {
    require(descending(l, k) && k >= 0)

   l match {
    case Nil() => Nil()
    case Cons(x, t) =>  {
      val f = fact(x)
      Cons(f, factMap(t, x-1))
    }

  }} ensuring(res => true && tmpl((a,b) => depth <= a*k + b))
}