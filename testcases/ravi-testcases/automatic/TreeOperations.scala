import leon.Utils._

object TreeOperations {

  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  sealed abstract class Tree
  case class Node(left: Tree, value: Int, right: Tree) extends Tree
  case class Leaf() extends Tree

  def listSize(l: List): Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + listSize(t)
  })

  def size(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        size(l) + size(r) + 1
      }
    }
  }

  def height(t: Tree): Int = {
    t match {
      case Leaf() => 0
      case Node(l, x, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  } 
  //ensuring(res => res != size(t) + 1 template((a,b,c)=> a*size(t) + b*res +c <= 0))

  def insert(elem: Int, t: Tree): Tree = {
    t match {
      case Leaf() => Node(Leaf(), elem, Leaf())
      case Node(l, x, r) => if (x <= elem) Node(l, x, insert(elem, r))
      else Node(insert(elem, l), x, r)
    }
  } 
  //ensuring (res => true template ((a, b, c) => a * size(t) + b * size(res) + c == 0))

  def addAll(l: List, t: Tree): Tree = {
    l match {
      case Nil() => t
      case Cons(x, xs) => addAll(xs, insert(x, t))
    }
  } ensuring (res => size(res) >= size(t))

  def remove(elem: Int, t: Tree): Tree = {
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
  } 
  //ensuring (res => true template ((a, b, c) => a * size(res) + b * size(t) + c <= 0))

  /*def removeAll(l: List, t: Tree): Tree = {
    l match {
      case Nil() => t
      case Cons(x, xs) => removeAll(xs, remove(x, t))
    }
  } ensuring (res => size(res) <= size(t))*/

/*  def contains(elem : Int, t : Tree) : Boolean = {
    t match {
      case Leaf() => false
      case Node(l, x, r) =>
        if(x == elem) true
        else if (x < elem) contains(elem, r)
        else contains(elem, l)
    }
  }*/
} 