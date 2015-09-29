import leon.invariant._
import leon.instrumentation._

object BinaryTrie {
  sealed abstract class Tree
  case class Leaf() extends Tree
  case class Node(nvalue: BigInt, left: Tree, right: Tree) extends Tree

  sealed abstract class IList
  case class Cons(head: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  def listSize(l: IList): BigInt = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + listSize(xs)
  })

  def height(t: Tree): BigInt = {
    t match {
      case Leaf() => 0
      case Node(x, l, r) => {
        val hl = height(l)
        val hr = height(r)
        if (hl > hr) hl + 1 else hr + 1
      }
    }
  }

  def find(inp: IList, t: Tree): Tree = {
    inp match {
      case Nil() => t
      case Cons(x, Nil()) => t
      case Cons(x, xs @ Cons(y, _)) => {
        t match {
          case Leaf() => t
          case Node(v, l, r) => {
            if (y > 0) find(xs, l) else find(xs, r)
          }
        }
      }
      case _ => t
    }
  } ensuring (_ => time <= ? * listSize(inp) + ?)

  def insert(inp: IList, t: Tree): Tree = {
    t match {
      case Leaf() => {
        inp match {
          case Nil() => t
          case Cons(x, xs) => {
            val newch = insert(xs, Leaf())
            newch match {
              case Leaf() => Node(x, Leaf(), Leaf())
              case Node(y, _, _) => if (y > 0) Node(x, newch, Leaf()) else Node(y, Leaf(), newch)
            }
          }
        }

      }
      case Node(v, l, r) => {
        inp match {
          case Nil() => t
          case Cons(x, Nil()) => t
          case Cons(x, xs @ Cons(y, _)) => {
            val ch = if (y > 0) l else r
            if (y > 0)
              Node(v, insert(xs, ch), r)
            else
              Node(v, l, insert(xs, ch))
          }
          case _ => t
        }
      }
    }
  } ensuring (_ => time <= ? * listSize(inp) + ?)

  def create(inp: IList): Tree = {
    insert(inp, Leaf())
  } ensuring (res => true && tmpl((a, c) => time <= a * listSize(inp) + c))

  def delete(inp: IList, t: Tree): Tree = {
    t match {
        case Leaf() => {
          inp match {
            case Nil() => Leaf()
            case Cons(x ,xs) => {
              //the input is not in the tree, so do nothing
              Leaf()
            }
          }
        }
        case Node(v, l, r) => {
          inp match {
            case Nil() => {
              //the tree has extensions of the input list so do nothing
              t
            }
            case Cons(x, Nil()) => {
              //if "l" and "r" are nil, remove the node
              if(l == Leaf() && r == Leaf()) Leaf()
              else t
            }
            case Cons(x ,xs@Cons(y, _)) => {
              val ch = if(y > 0) l else r
              val newch = delete(xs, ch)
              if(newch == Leaf() && ((y > 0 && r == Leaf()) || (y <= 0 && l == Leaf()))) Leaf()
              else {
                if(y > 0)
        		  Node(v, newch, r)
        	    else
        	      Node(v, l, newch)
              }
            }
            case _ => t
        }
      }
    }
  } ensuring (_ => time <= ? * listSize(inp) + ?)
}
