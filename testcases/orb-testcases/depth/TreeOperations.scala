import leon.instrumentation._
import leon.invariant._
import leon.annotation._

object TreeOperations {

  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Tree
  case class Node(left: Tree, value: BigInt, right: Tree) extends Tree
  case class Leaf() extends Tree

  def listSize(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + listSize(t)
  })

  def size(t: Tree): BigInt = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        size(l) + size(r) + 1
      }
    }
  }

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

  def insert(elem: BigInt, t: Tree): Tree = {
    t match {
      case Leaf() => Node(Leaf(), elem, Leaf())
      case Node(l, x, r) => if (x <= elem) Node(l, x, insert(elem, r))
      else Node(insert(elem, l), x, r)
    }
  } ensuring (res => height(res) <= height(t) + 1 && tmpl((a,b) => depth <= a*height(t) + b))

  def addAll(l: List, t: Tree): Tree = {
    l match {
      case Nil() => t
      case Cons(x, xs) =>{
        val newt = insert(x, t)
        addAll(xs, newt)
      }
    }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*(listSize(l) * (height(t) + listSize(l))) + b*listSize(l) + c))

  def remove(elem: BigInt, t: Tree): Tree = {
    t match {
      case Leaf() => Leaf()
      case Node(l, x, r) => {

        if (x < elem) Node(l, x, remove(elem, r))
        else if (x > elem) Node(remove(elem, l), x, r)
        else {
          t match {
            case Node(Leaf(), x, Leaf()) => Leaf()
            case Node(Leaf(), x, Node(_, rx, _)) => Node(Leaf(), rx, remove(rx, r))
            case Node(Node(_, lx, _), x, r) => Node(remove(lx, l), lx, r)
            case _ => Leaf()
          }
        }
      }
    }
  } ensuring (res => height(res) <= height(t) && tmpl ((a, b, c) => depth <= a*height(t) + b))

  def removeAll(l: List, t: Tree): Tree = {
    l match {
      case Nil() => t
      case Cons(x, xs) => removeAll(xs, remove(x, t))
    }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*(listSize(l) * height(t)) + b*listSize(l) + c))

  def contains(elem : BigInt, t : Tree) : Boolean = {
    t match {
      case Leaf() => false
      case Node(l, x, r) =>
        if(x == elem) true
        else if (x < elem) contains(elem, r)
        else contains(elem, l)
    }
  } ensuring (res => true && tmpl((a,b) => depth <= a*height(t) + b))
}