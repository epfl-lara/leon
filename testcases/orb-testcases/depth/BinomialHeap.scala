/**
 * @author Ravi
 **/
import leon.instrumentation._
import leon.invariant._


object BinomialHeap {
  sealed abstract class BinomialTree
  case class Node(rank: BigInt, elem: Element, children: BinomialHeap) extends BinomialTree

  sealed abstract class ElementAbs
  case class Element(n: BigInt) extends ElementAbs

  sealed abstract class BinomialHeap
  case class ConsHeap(head: BinomialTree, tail: BinomialHeap) extends BinomialHeap
  case class NilHeap() extends BinomialHeap

  sealed abstract class List
  case class NodeL(head: BinomialHeap, tail: List) extends List
  case class NilL() extends List

  sealed abstract class OptionalTree
  case class Some(t : BinomialTree) extends OptionalTree
  case class None() extends OptionalTree

  /* Lower or Equal than for Element structure */
  private def leq(a: Element, b: Element) : Boolean = {
    a match {
      case Element(a1) => {
        b match {
          case Element(a2) => {
            if(a1 <= a2) true
            else false
          }
        }
      }
    }
  }

  /* isEmpty function of the Binomial Heap */
  def isEmpty(t: BinomialHeap) = t match {
    case ConsHeap(_,_) => false
    case NilHeap() => true
  }

  /* Helper function to determine rank of a BinomialTree */
  def rank(t: BinomialTree) : BigInt =  t match {
    case Node(r, _, _) => r
  }

  /* Helper function to get the root element of a BinomialTree */
  def root(t: BinomialTree) : Element = t match {
    case Node(_, e, _) => e
  }

  /* Linking trees of equal ranks depending on the root element */
  def link(t1: BinomialTree, t2: BinomialTree) : BinomialTree = {
    t1 match {
        case Node(r, x1, c1) => {
          t2 match {
            case Node(_, x2, c2) => {
              if (leq(x1,x2)) {
                  Node(r+1, x1, ConsHeap(t2, c1))
              } else {
                  Node(r+1, x2, ConsHeap(t1, c2))
              }
            }
          }
        }
    }
  }

  def treeNum(h: BinomialHeap) : BigInt = {
    h match {
      case ConsHeap(head, tail) =>  1 + treeNum(tail)
      case NilHeap() => 0
    }
  }

  /* Insert a tree into a binomial heap. The tree should be correct in relation to the heap */
  def insTree(t: BinomialTree, h: BinomialHeap) : BinomialHeap = {
    h match {
      case ConsHeap(head, tail) =>  {
        if (rank(t) < rank(head)) {
          ConsHeap(t, h)
        } else if (rank(t) > rank(head)) {
          ConsHeap(head, insTree(t,tail))
        } else {
          insTree(link(t,head), tail)
        }
      }
      case NilHeap() => ConsHeap(t, NilHeap())
    }
  } ensuring(res => true && tmpl((a,b) => depth <= a*treeNum(h) + b))

  /* Merge two heaps together */
  def merge(h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    h1 match {
      case ConsHeap(head1, tail1) => {
        h2 match {
          case ConsHeap(head2, tail2) => {
            if (rank(head1) < rank(head2)) {
              ConsHeap(head1, merge(tail1, h2))
            } else if (rank(head2) < rank(head1)) {
              ConsHeap(head2, merge(h1, tail2))
            } else {
              mergeWithCarry(link(head1, head2), tail1, tail2)
            }
          }
          case NilHeap() => h1
        }
      }
      case NilHeap() => h2
    }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*treeNum(h1) + b*treeNum(h2) + c))

  def mergeWithCarry(t: BinomialTree, h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    t match {
      case Node(r, _, _) => {
        h1 match {
          case ConsHeap(head1, tail1) => {
            h2 match {
              case ConsHeap(head2, tail2) => {
                if (rank(head1) < rank(head2)) {

                  if (rank(t) < rank(head1))
                    ConsHeap(t, ConsHeap(head1, merge(tail1, h2)))
                  else
                    mergeWithCarry(link(t, head1), tail1, h2)

                } else if (rank(head2) < rank(head1)) {

                  if (rank(t) < rank(head2))
                    ConsHeap(t, ConsHeap(head2, merge(h1, tail2)))
                  else
                    mergeWithCarry(link(t, head2), h1, tail2)

                } else {
                  ConsHeap(t, mergeWithCarry(link(head1, head2), tail1, tail2))
                }
              }
              case NilHeap() => {
                insTree(t, h1)
              }
            }
          }
          case NilHeap() => insTree(t, h2)
        }
      }
    }
  } ensuring (res => true && tmpl ((d, e, f) => depth <= d * treeNum(h1) + e * treeNum(h2) + f))

  //Auxiliary helper function to simplify findMin and deleteMin
  def removeMinTree(h: BinomialHeap): (OptionalTree, BinomialHeap) = {
    h match {
      case ConsHeap(head, NilHeap()) => (Some(head), NilHeap())
      case ConsHeap(head1, tail1) => {
        val (opthead2, tail2) = removeMinTree(tail1)
        opthead2 match {
          case None() => (Some(head1), tail1)
          case Some(head2) =>
            if (leq(root(head1), root(head2))) {
              (Some(head1), tail1)
            } else {
              (Some(head2), ConsHeap(head1, tail2))
            }
        }
      }
      case _ => (None(), NilHeap())
    }
  } ensuring (res => treeNum(res._2) <= treeNum(h) && tmpl ((a, b) => depth <= a*treeNum(h) + b))

  /*def findMin(h: BinomialHeap) : Element = {
	  val (opt, _) = removeMinTree(h)
	  opt match {
	    case Some(Node(_,e,ts1)) => e
	    case _ => Element(-1)
	  }
  } ensuring(res => true && tmpl((a,b) => time <= a*treeNum(h) + b))*/

  def minTreeChildren(h: BinomialHeap) : BigInt = {
    val (min, _) = removeMinTree(h)
    min match {
      case None() => 0
      case Some(Node(_,_,ch)) => treeNum(ch)
	}
  }

  // Discard the minimum element of the extracted min tree and put its children back into the heap
  def deleteMin(h: BinomialHeap) : BinomialHeap = {
	  val (min, ts2) = removeMinTree(h)
	  min match {
		case Some(Node(_,_,ts1)) => merge(ts1, ts2)
		case _ => h
	  }
  } ensuring(res => true && tmpl((a,b,c) => depth <= a*minTreeChildren(h) + b*treeNum(h) + c))

}
