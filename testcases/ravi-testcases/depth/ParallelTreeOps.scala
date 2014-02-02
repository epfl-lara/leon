import leon.Utils._

object ParllelTreeOps {

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
  
  def parallelSearch(elem : Int, t : Tree) : Boolean = {
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
  } ensuring(res => true template((a,b) => depth <= a*height(t) + b))
  
 
  def squareMap(t : Tree) : Tree = {
    t match {
      case Leaf() => t
      case Node(l, x, r) =>
        val nl = squareMap(l)
        val nr = squareMap(r)
        Node(nl, x*x, nr)
    }
  } ensuring (res => true template((a,b) => depth <= a*height(t) + b))  
} 