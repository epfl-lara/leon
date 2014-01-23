/** 
 * Okasaki3_2
 * 
 * Based on the chapter 3.2 of Okasaki's paper Purely Functional Data Structure
 * Implements the "Binomial Heap" data structure described in the chapter.
 * 
 * @author Florian Briant
 **/

import leon.Utils._
import leon.Annotations._

object BinomialHeap {    
  sealed abstract class BinomialTree
  case class Node(rank: Int, elem: Element, children: BinomialHeap) extends BinomialTree
  
  sealed abstract class Carry 
  case class NilCarry() extends Carry
  case class Some(tree: BinomialTree) extends Carry
  
  sealed abstract class ElementAbs
  case class Element(n: Int) extends ElementAbs
  
  sealed abstract class BinomialHeap
  case class ConsHeap(head: BinomialTree, tail: BinomialHeap) extends BinomialHeap
  case class NilHeap extends BinomialHeap
  
  sealed abstract class List
  case class NodeL(head: BinomialHeap, tail: List) extends List
  case class NilL() extends List
  
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
  def rank(t: BinomialTree) : Int =  t match {
    case Node(r, _, _) => r
  }
  
  /* Helper function to get the root element of a BinomialTree */
  def root(t: BinomialTree) : Element = t match {
    case Node(_, e, _) => e
  }
  
  /* Helper function which tell if a binomial tree is valid */
  /*private def isBinomialTreeValid(l: BinomialTree) : Boolean = l match {
    case Node(r, e, c) => {
      def checkChildren(index: Int, origRank: Int, origElem: Element, children: BinomialHeap) : Boolean = children match {
        case ConsHeap(h,t) => h match {
          case Node(r1,e1,_) => leq(origElem, e1) && r1 == origRank - index - 1 && isBinomialTreeValid(h) && checkChildren(index + 1, origRank, origElem, t)
        }
        case NilHeap() => index == origRank
      }
      checkChildren(0, r, e, c)
    }
  }
  
   Helper function which tell if a binomial heap is valid 
  private def isBinomialHeapValid(h: BinomialHeap) : Boolean ={
    def isBinomialHeapValidStep(h1: BinomialHeap, oldR: Int) : Boolean = h1 match {
      case ConsHeap(e, tail) => oldR < rank(e) && isBinomialHeapValidStep(tail, rank(e)) && isBinomialTreeValid(e)
      case NilHeap() => true
    }
    isBinomialHeapValidStep(h, -1)
  }*/
  
  /*private def rankIncrease(h: BinomialHeap) : Boolean = {
    h match {
      case ConsHeap(tr, tail) => {        
        tail match{ 
          case ConsHeap(tr2, tail2) => tr < tr2 && rankIncrease(tail)
          case NilHeap => true
        }        
        rank(tr) < heapRank(tail) && rankIncrease(tail)
      } 
      case NilHeap() => true
    }
  }*/
  
  /* Linking trees of equal ranks depending on the root element */ 
  def link(t1: BinomialTree, t2: BinomialTree) : BinomialTree = {
    //require(isBinomialTreeValid(t1) && isBinomialTreeValid(t2) && rank(t1) == rank(t2))
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
  } //ensuring(res => isBinomialTreeValid(res))
  
  /* Helper function to validate the input tree of insTree */
  /*private def isTreeValidForInsert(t: BinomialTree, h: BinomialHeap) = h match {
    case ConsHeap(head, tail) => rank(t) <= rank(head) 
    case NilHeap() => true
  }*/
  
  def treeNum(h: BinomialHeap) : Int = {
    h match {
      case ConsHeap(head, tail) =>  1 + treeNum(tail)
      case NilHeap() => 0
    }
  }
  
  /* Insert a tree into a binomial heap. The tree should be correct in relation to the heap */
  def insTree(t: BinomialTree, h: BinomialHeap) : BinomialHeap = {
    //require(isBinomialTreeValid(t) && isBinomialHeapValid(h) && isTreeValidForInsert(t,h))    
    h match {
      case ConsHeap(head, tail) =>  {
        if (rank(t) < rank(head)) {
          ConsHeap(t, h)
        } else {
          insTree(link(t,head), tail)
        }
      }
      case NilHeap() => ConsHeap(t, NilHeap())
    }
  } ensuring(res => true template((a,b) => time <= a*treeNum(h) + b))
  //ensuring(res => isBinomialHeapValid(res))
  
  /*def mult(x : Int, y : Int) : Int = {
      if(x == 0 || y == 0) 0
      else
    	  mult(x-1,y-1) + x + y -1
  }*/
  
  /* Merge two heaps together */  
  /*def merge(h1: BinomialHeap, h2: BinomialHeap) : BinomialHeap = {
    //require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2))
    require(rankIncrease(h1) && rankIncrease(h2))
    h1 match {
      case ConsHeap(head1, tail1) => {
        h2 match {
          case ConsHeap(head2, tail2) => {
            if (rank(head1) < rank(head2)) {
              ConsHeap(head1, merge(tail1, h2))
            } else if (rank(head2) < rank(head1)) {
              ConsHeap(head2, merge(h1, tail2))
            } else {
              insTree(link(head1, head2), merge(tail1, tail2))
            }
          }
          case NilHeap() => h1
        }
      }
      case NilHeap() => h2
    }
  } ensuring(res => (treeNum(res)<=treeNum(h1)+treeNum(h2) && rankIncrease(res) && heapRank(res)>=min(heapRank(h1),heapRank(h2))) 
      template((b,c,d) => time <= b*treeNum(h1) + c*treeNum(h2) + d))*/
  //ensuring(res => treeNum(res)<=treeNum(h1)+treeNum(h2) template((a,b,c,d) => time <= a*mult(treeNum(h1),treeNum(h2)) + b*treeNum(h1) + c*treeNum(h2) + d))
  //((((((2 * res4._2) + (-2 * treeNum2(h2))) + (-1 * treeNum2(h1))) + (-74 * mult2(treeNum2(h1), treeNum2(h2)))) + -6) <= 0)
  //ensuring(res => isBinomialHeapValid(res))
      
  /* Merge two heaps together */  
  def merge(h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    //require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2))    
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
  } ensuring(res => true template((a,b,c) => time <= a*treeNum(h1) + b*treeNum(h2) + c))

  def mergeWithCarry(t: BinomialTree, h1: BinomialHeap, h2: BinomialHeap): BinomialHeap = {
    //require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2))    
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
                    ConsHeap(link(t, head1), merge(tail1, h2))
                  
                } else if (rank(head2) < rank(head1)) {
                  
                  if (rank(t) < rank(head2))
                    ConsHeap(t, ConsHeap(head2, merge(h1, tail2)))
                  else 
                    ConsHeap(link(t, head2), merge(h1, tail2))
                  
                } else {
                  ConsHeap(t, mergeWithCarry(link(head1, head2), tail1, tail2))
                }
              }
              case NilHeap() => {
                insTree(link(t, head1), tail1)
              }
            }
          }
          case NilHeap() => insTree(t, h2)
        }
      }
    }
  } ensuring (res => true template ((d, e, f) => time <= d * treeNum(h1) + e * treeNum(h2) + f)) 

  /* Helper function to define ensuring clause in removeMinTree */
  /*private def isRemovedMinTreeValid(x : (BinomialTree, BinomialHeap)) : Boolean = {
    val (t,h) = x
    isBinomialTreeValid(t) && isBinomialHeapValid(h)
  }

   Auxiliary helper function to simplefy findMin and deleteMin 
  def removeMinTree(h: BinomialHeap) : (BinomialTree, BinomialHeap) = {
    require(isBinomialHeapValid(h) && !isEmpty(h))
    h match {
      case ConsHeap(head, NilHeap()) => (head, NilHeap())
      case ConsHeap(head1, tail1) => {
        val (head2, tail2) = removeMinTree(tail1)
        if (leq(root(head1), root(head2))) {
          (head1, tail1)
        } else {
          (head2, ConsHeap(head1, tail2))
        }
      }
    }
  } ensuring(res => isRemovedMinTreeValid(res))
  
   Returns the root as the extracted min tree 
  def findMin(h: BinomialHeap) : Element = {
	  require(isBinomialHeapValid(h) && !isEmpty(h))
	  val (t, _) = removeMinTree(h)
	  root(t)
  }
  
   Helper function to concat twos list 
  private def concat(l1: BinomialHeap, l2: BinomialHeap) : BinomialHeap = l1 match {
    case NilHeap() => l2
    case ConsHeap(x, xs) => ConsHeap(x, concat(xs, l2))
  }
  
   Helper function to reverse a list 
  private def rev(l: BinomialHeap) : BinomialHeap = l match {
	  case NilHeap() => NilHeap()
	  case ConsHeap(x, xs) => concat(rev(xs), ConsHeap(x, NilHeap()))
  }
  
   Discard the minimum element of the extracted min tree and put its children back into the heap 
  def deleteMin(h: BinomialHeap) : BinomialHeap = {
	  require(isBinomialHeapValid(h) && !isEmpty(h))
	  val (min, ts2) = removeMinTree(h)
	  min match {
		  case Node(_,_,ts1) => merge(rev(ts1), ts2)
	  }
  } ensuring(res => isBinomialHeapValid(h))
  
   SORT AREA 
  
   Tells if a list of BinomialHeap is empty 
  def isEmptyList(l: List) = l match {
    case NodeL(_,_) => false
    case NilL() => true
  }
   Gives the head of a list 
  def head(l: List) = {
    require(!isEmptyList(l))
    l match {
      case NodeL(h,_) => h
    }
  }
   Gives the tail of a list 
  def tail(l: List) = {
    require(!isEmptyList(l))
    l match {
      case NodeL(_,t) => t
    }
  }
   Lower than Equal between two heaps, comparing their min element 
  def leqValueHeap(h1: BinomialHeap, h2: BinomialHeap) : Boolean = {
    require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2) && !isEmpty(h1) && !isEmpty(h2))
    leq(findMin(h1), findMin(h2))
  }
  
   Gives the last tree of a binomial heap 
  private def getLastTree(h1: BinomialHeap) : BinomialTree = {
    require(!isEmpty(h1))
    h1 match {
      case ConsHeap(h, NilHeap()) => h
      case ConsHeap(_,t) => getLastTree(t)
    }
  }
   Compare two heaps by their binary representations 
  def leqBinaryHeap(h1: BinomialHeap, h2: BinomialHeap) : Boolean = {
    require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2) && !isEmpty(h1) && !isEmpty(h2))
    if (rank(getLastTree(h1)) < rank(getLastTree(h2))) {
      true
    } else if (rank(getLastTree(h1)) == rank(getLastTree(h2))) {
      leq(root(getLastTree(h1)), root(getLastTree(h2)))
    } else {
      false
    }
  }
   Compare two heaps and swaps them if the first has an higher first element or if we consider the binary comparison
  private def swap(h1: BinomialHeap, h2: BinomialHeap, binary: Boolean) : (BinomialHeap, BinomialHeap) = {
    require(isBinomialHeapValid(h1) && isBinomialHeapValid(h2) && !isEmpty(h1) && !isEmpty(h2))
    if (binary) {
      if (leqBinaryHeap(h1,h2)) {
        (h1,h2) 
      } else {
        (h2,h1)
      }
    }
    else {
      if (leqValueHeap(h1,h2)) {
        (h1,h2) 
      } else {
        (h2,h1)
      }
    }
  } ensuring (res => isBinomialHeapValid(res._1) && isBinomialHeapValid(res._2) && !isEmpty(res._1) && !isEmpty(res._2))
  
   Tells if a list contains only valid BinomialHeap 
  private def isListValid(l: List) : Boolean = l match {
    case NodeL(h,t) => isBinomialHeapValid(h) && !isEmpty(h) && isListValid(t)
    case NilL() => true
  }
  
   Delete the last element of the list and gives it back 
  private def delLast(l: List) : (BinomialHeap, List) = {
    require(!isEmptyList(l))
    l match {
      case NodeL(h, NilL()) => (h, NilL())
      case NodeL(h,t) => {
        val dl = delLast(t)
        (dl._1, NodeL(h, dl._2))
      }
      case NilL() => (NilHeap(), NilL())
    }
  }
  
   Do one step of the bubble sort algorithm. Result list has its highest element at the end 
  private def bubbleSortStep(l: List, binary: Boolean) : List = {
    require(isListValid(l))
    l match {
      case NodeL(h, NilL()) => NodeL(h, NilL())
      case NodeL(h,t) => {
        val sw = swap(h, head(t), binary)
        NodeL(sw._1, bubbleSortStep(NodeL(sw._2, tail(t)), binary))
      }
      case NilL() => NilL()
    }
  } ensuring(res => isListValid(res))
  
   Concatenate two lists 
  private def concat(l1: List, l2: List) : List = l1 match {
    case NilL() => l2
    case NodeL(x, xs) => NodeL(x, concat(xs, l2))
  }
  
   Do the buble sort algorithm 
  def bubbleSort(l: List, binary: Boolean) : List = {
    require(isListValid(l))
    l match {
      case NodeL(h, NilL()) => l
      case NodeL(h, t) => {
        val dl = delLast(bubbleSortStep(l, binary))
        concat(bubbleSort(dl._2, binary), NodeL(dl._1, NilL()))
      }
      case NilL() => NilL()
    }

  } ensuring(res => isListValid(res))
*/  
  /* TEST AREA */
  
  /*def BTtest1() : Boolean = isBinomialTreeValid(Node(1, Element(2), ConsHeap(Node(0, Element(3), NilHeap()),NilHeap())))*/ 
  /*def BTtest2() : Boolean = isBinomialTreeValid(Node(0, Element(3), NilHeap()))*/
  /*def BTtest3() : Boolean = isBinomialTreeValid(Node(1, Element(975), ConsHeap(Node(0, Element(976), NilHeap()), NilHeap())))*/
  /*def BHtest1() : Boolean = isBinomialHeapValid(ConsHeap(Node(0, Element(0), Nil()),ConsHeap(Node(1, Element(0), ConsHeap(Node(0, Element(1), NilHeap()),NilHeap())),NilHeap())))*/
  /*def testInsTree1() : BinomialHeap = insTree(Node(0, Element(2), NilHeap()), ConsHeap(Node(1, Element(3), ConsHeap(Node(0, Element(4), NilHeap()),NilHeap())),NilHeap()))*/
  /*def testInsTree2() : BinomialHeap = insTree(Node(0, Element(2), NilHeap()), ConsHeap(Node(0, Element(1), NilHeap()), NilHeap()))*/
  
  /*def testMerge1() : BinomialHeap = merge(ConsHeap(Node(0, Element(1), NilHeap()), NilHeap()), ConsHeap(Node(1, Element(3), ConsHeap(Node(0, Element(4), NilHeap()),NilHeap())),NilHeap()))*/
  /*def testMerge2() : BinomialHeap = merge(ConsHeap(Node(1, Element(2), ConsHeap(Node(0, Element(4), NilHeap()),NilHeap())),NilHeap()), ConsHeap(Node(0, Element(3), NilHeap()), NilHeap()))*/
  /*def testMerge3() : BinomialHeap = merge(ConsHeap(Node(0, Element(4), NilHeap()), NilHeap()), ConsHeap(Node(0, Element(1), NilHeap()), NilHeap()))*/
  
  /*def testRemoveMinTree1() : (BinomialTree, BinomialHeap) = removeMinTree(ConsHeap(Node(0, Element(1), NilHeap()), NilHeap()))
  def testRemoveMinTree2() : (BinomialTree, BinomialHeap) = removeMinTree(testMerge1())
  def testRemoveMinTree3() : (BinomialTree, BinomialHeap) = removeMinTree(testMerge2())*/
  
  /*def testFindMin1() : Element = findMin(testMerge1())
  
  def testConcat : List = concat(ConsHeap(Node(0, Element(0), NilHeap()), NilHeap()), ConsHeap(Node(0, Element(0), NilHeap()), ConsHeap(Node(0, Element(0), NilHeap()), NilHeap())))
  
  def testRev: List = rev(ConsHeap(Node(0, Element(0), NilHeap()), ConsHeap(Node(1, Element(1), NilHeap()),ConsHeap(Node(2, Element(2), NilHeap()),NilHeap()))))*/
  
  /*def testDeleteMin1() = deleteMin(testMerge1())*/
  
  /*def sortTest() = bubbleSort(NodeL(testMerge1(), NodeL(testMerge2(), NilL())), true)
  def sortTest2() = bubbleSort(NodeL(testMerge1(), NodeL(testMerge2(), NilL())), false)*/
 
  
  
}
