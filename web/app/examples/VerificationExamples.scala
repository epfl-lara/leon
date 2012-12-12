package examples

object VerificationExamples {
  var allExamples = List[Example]()

  def newExample(title: String, code: String) {
    allExamples = allExamples ::: Example(title, "verification", code) :: Nil
  }

  val default = Example("Default", "verification", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object Example {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  /* ... */

}
  """.trim)

  newExample("Amortized Queue", """
import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
  
  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && content(res) == content(l1) ++ content(l2))

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil(), Nil()) => true
    case _ => false
  }

  def reverse(l : List) : List = (l match {
    case Nil() => Nil()
    case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil()))
  }) ensuring (content(_) == content(l))

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } ensuring(isAmortized(_))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(isAmortized(_))

  def tail(queue : AbsQueue) : AbsQueue = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  } ensuring (isAmortized(_))

  def front(queue : AbsQueue) : Int = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }

  @induct
  def propFront(queue : AbsQueue, list : List, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (asList(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  } holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  } holds

  def enqueueDequeueThrice(queue : AbsQueue, e1 : Int, e2 : Int, e3 : Int) : Boolean = {
    if (isEmpty(queue)) {
      val q1 = enqueue(queue, e1)
      val q2 = enqueue(q1, e2)
      val q3 = enqueue(q2, e3)
      val e1prime = front(q3)
      val q4 = tail(q3)
      val e2prime = front(q4)
      val q5 = tail(q4)
      val e3prime = front(q5)
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  } holds
}""".trim)

  newExample("Associative List", """
import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object AssociativeList { 
  sealed abstract class KeyValuePairAbs
  case class KeyValuePair(key: Int, value: Int) extends KeyValuePairAbs

  sealed abstract class List
  case class Cons(head: KeyValuePairAbs, tail: List) extends List
  case class Nil() extends List

  sealed abstract class OptionInt
  case class Some(i: Int) extends OptionInt
  case class None() extends OptionInt

  def domain(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(KeyValuePair(k,_), xs) => Set(k) ++ domain(xs)
  }

  def find(l: List, e: Int): OptionInt = l match {
    case Nil() => None()
    case Cons(KeyValuePair(k, v), xs) => if (k == e) Some(v) else find(xs, e)
  }

  def noDuplicates(l: List): Boolean = l match {
    case Nil() => true
    case Cons(KeyValuePair(k, v), xs) => find(xs, k) == None() && noDuplicates(xs)
  }

  def update(l1: List, l2: List): List = (l2 match {
    case Nil() => l1
    case Cons(x, xs) => update(updateElem(l1, x), xs)
  }) ensuring(domain(_) == domain(l1) ++ domain(l2))

  def updateElem(l: List, e: KeyValuePairAbs): List = (l match {
    case Nil() => Cons(e, Nil())
    case Cons(KeyValuePair(k, v), xs) => e match {
      case KeyValuePair(ek, ev) => if (ek == k) Cons(KeyValuePair(ek, ev), xs) else Cons(KeyValuePair(k, v), updateElem(xs, e))
    }
  }) ensuring(res => e match {
    case KeyValuePair(k, v) => domain(res) == domain(l) ++ Set[Int](k)
  })

  @induct
  def readOverWrite(l: List, k1: Int, k2: Int, e: Int) : Boolean = {
    find(updateElem(l, KeyValuePair(k2,e)), k1) == (if (k1 == k2) Some(e) else find(l, k1))
  } holds
}
  """.trim)

  newExample("Insertion Sort", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object InsertionSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  sealed abstract class OptInt
  case class Some(value: Int) extends OptInt
  case class None() extends OptInt

  def size(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }   

  /* Inserting element 'e' into a sorted list 'l' produces a sorted list with
   * the expected content and size */
  def sortedIns(e: Int, l: List): List = {
    require(isSorted(l))
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,sortedIns(e, xs)) else Cons(e, l)
    } 
  } ensuring(res => contents(res) == contents(l) ++ Set(e) 
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* A counterexample is found when we forget to specify the precondition */
  def buggySortedIns(e: Int, l: List): List = {
    l match {
      case Nil() => Cons(e,Nil())
      case Cons(x,xs) => if (x <= e) Cons(x,buggySortedIns(e, xs)) else Cons(e, l)
    } 
  } ensuring(res => contents(res) == contents(l) ++ Set(e) 
                    && isSorted(res)
                    && size(res) == size(l) + 1
            )

  /* Insertion sort yields a sorted list of same size and content as the input
   * list */
  def sort(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sort(xs))
  }) ensuring(res => contents(res) == contents(l) 
                     && isSorted(res)
                     && size(res) == size(l)
             )

  /* Merges one (unsorted) list into another, sorted, list. */
  def mergeInto(l1 : List, l2 : List) : List = {
    require(isSorted(l2))
    l1 match {
      case Nil() => l2
      case Cons(x, xs) => mergeInto(xs, sortedIns(x, l2))
    }
  } ensuring(res => contents(res) == contents(l1) ++ contents(l2) && isSorted(res))

  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(sort(ls))
  }
}
  """.trim)

  newExample("List Operations", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object ListOperations {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    sealed abstract class IntPairList
    case class IPCons(head: IntPair, tail: IntPairList) extends IntPairList
    case class IPNil() extends IntPairList

    sealed abstract class IntPair
    case class IP(fst: Int, snd: Int) extends IntPair

    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    def iplSize(l: IntPairList) : Int = (l match {
      case IPNil() => 0
      case IPCons(_, xs) => 1 + iplSize(xs)
    }) ensuring(_ >= 0)

    def zip(l1: List, l2: List) : IntPairList = {
      // try to comment this and see how pattern-matching becomes
      // non-exhaustive and post-condition fails
      require(size(l1) == size(l2))

      l1 match {
        case Nil() => IPNil()
        case Cons(x, xs) => l2 match {
          case Cons(y, ys) => IPCons(IP(x, y), zip(xs, ys))
        }
      }
    } ensuring(iplSize(_) == size(l1))

    def sizeTailRec(l: List) : Int = sizeTailRecAcc(l, 0)
    def sizeTailRecAcc(l: List, acc: Int) : Int = {
     require(acc >= 0)
     l match {
       case Nil() => acc
       case Cons(_, xs) => sizeTailRecAcc(xs, acc+1)
     }
    } ensuring(res => res == size(l) + acc)

    def sizesAreEquiv(l: List) : Boolean = {
      size(l) == sizeTailRec(l)
    } holds

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    def sizeAndContent(l: List) : Boolean = {
      size(l) == 0 || content(l) != Set.empty[Int]
    } holds
    
    def drunk(l : List) : List = (l match {
      case Nil() => Nil()
      case Cons(x,l1) => Cons(x,Cons(x,drunk(l1)))
    }) ensuring (size(_) == 2 * size(l))

    def reverse(l: List) : List = reverse0(l, Nil()) ensuring(content(_) == content(l))
    def reverse0(l1: List, l2: List) : List = (l1 match {
      case Nil() => l2
      case Cons(x, xs) => reverse0(xs, Cons(x, l2))
    }) ensuring(content(_) == content(l1) ++ content(l2))

    def append(l1 : List, l2 : List) : List = (l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x, append(xs, l2))
    }) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def nilAppend(l : List) : Boolean = (append(l, Nil()) == l) holds

    @induct
    def appendAssoc(xs : List, ys : List, zs : List) : Boolean =
      (append(append(xs, ys), zs) == append(xs, append(ys, zs))) holds

    def revAuxBroken(l1 : List, e : Int, l2 : List) : Boolean = {
      (append(reverse(l1), Cons(e,l2)) == reverse0(l1, l2))
    } holds

    @induct
    def sizeAppend(l1 : List, l2 : List) : Boolean =
      (size(append(l1, l2)) == size(l1) + size(l2)) holds

    @induct
    def concat(l1: List, l2: List) : List = 
      concat0(l1, l2, Nil()) ensuring(content(_) == content(l1) ++ content(l2))

    @induct
    def concat0(l1: List, l2: List, l3: List) : List = (l1 match {
      case Nil() => l2 match {
        case Nil() => reverse(l3)
        case Cons(y, ys) => {
          concat0(Nil(), ys, Cons(y, l3))
        }
      }
      case Cons(x, xs) => concat0(xs, l2, Cons(x, l3))
    }) ensuring(content(_) == content(l1) ++ content(l2) ++ content(l3))
}
  """.trim)

  newExample("Propositional Logic", """
import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object PropositionalLogic { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }) ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }

  def nnf(formula: Formula): Formula = (formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Implies(lhs, rhs) => Implies(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
  }) ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }

  def evalLit(id : Int) : Boolean = (id == 42) // could be any function
  def eval(f: Formula) : Boolean = f match {
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs) => eval(lhs) || eval(rhs)
    case Implies(lhs, rhs) => !eval(lhs) || eval(rhs)
    case Not(f) => !eval(f)
    case Literal(id) => evalLit(id)
  }
  
  @induct
  def simplifySemantics(f: Formula) : Boolean = {
    eval(f) == eval(simplify(f))
  } holds

  // Note that matching is exhaustive due to precondition.
  def vars(f: Formula): Set[Int] = {
    require(isNNF(f))
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Implies(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[Int](i)
      case Literal(i) => Set[Int](i)
    }
  }

  def fv(f : Formula) = { vars(nnf(f)) }

  @induct
  def wrongCommutative(f: Formula) : Boolean = {
    nnf(simplify(f)) == simplify(nnf(f))
  } holds

  @induct
  def simplifyBreaksNNF(f: Formula) : Boolean = {
    require(isNNF(f))
    isNNF(simplify(f))
  } holds

  @induct
  def nnfIsStable(f: Formula) : Boolean = {
    require(isNNF(f))
    nnf(f) == f
  } holds
  
  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  } holds
}
  """.trim)

  newExample("Red-Black Tree", """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object RedBlackTree { 
  sealed abstract class Color
  case class Red() extends Color
  case class Black() extends Color
 
  sealed abstract class Tree
  case class Empty() extends Tree
  case class Node(color: Color, left: Tree, value: Int, right: Tree) extends Tree

  sealed abstract class OptionInt
  case class Some(v : Int) extends OptionInt
  case class None() extends OptionInt

  def content(t: Tree) : Set[Int] = t match {
    case Empty() => Set.empty
    case Node(_, l, v, r) => content(l) ++ Set(v) ++ content(r)
  }

  def size(t: Tree) : Int = t match {
    case Empty() => 0
    case Node(_, l, v, r) => size(l) + 1 + size(r)
  }

  /* We consider leaves to be black by definition */
  def isBlack(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(),_,_,_) => true
    case _ => false
  }

  def redNodesHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(Black(), l, _, r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
    case Node(Red(), l, _, r) => isBlack(l) && isBlack(r) && redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def redDescHaveBlackChildren(t: Tree) : Boolean = t match {
    case Empty() => true
    case Node(_,l,_,r) => redNodesHaveBlackChildren(l) && redNodesHaveBlackChildren(r)
  }

  def blackBalanced(t : Tree) : Boolean = t match {
    case Node(_,l,_,r) => blackBalanced(l) && blackBalanced(r) && blackHeight(l) == blackHeight(r)
    case Empty() => true
  }

  def blackHeight(t : Tree) : Int = t match {
    case Empty() => 1
    case Node(Black(), l, _, _) => blackHeight(l) + 1
    case Node(Red(), l, _, _) => blackHeight(l)
  }

  // <<insert element x into the tree t>>
  def ins(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    t match {
      case Empty() => Node(Red(),Empty(),x,Empty())
      case Node(c,a,y,b) =>
        if      (x < y)  balance(c, ins(x, a), y, b)
        else if (x == y) Node(c,a,y,b)
        else             balance(c,a,y,ins(x, b))
    }
  } ensuring (res => content(res) == content(t) ++ Set(x) 
                   && size(t) <= size(res) && size(res) <= size(t) + 1
                   && redDescHaveBlackChildren(res)
                   && blackBalanced(res))

  def makeBlack(n: Tree): Tree = {
    require(redDescHaveBlackChildren(n) && blackBalanced(n))
    n match {
      case Node(Red(),l,v,r) => Node(Black(),l,v,r)
      case _ => n
    }
  } ensuring(res => redNodesHaveBlackChildren(res) && blackBalanced(res))

  def add(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t) && blackBalanced(t))
    makeBlack(ins(x, t))
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res) && blackBalanced(res))
  
  def buggyAdd(x: Int, t: Tree): Tree = {
    require(redNodesHaveBlackChildren(t))
    ins(x, t)
  } ensuring (res => content(res) == content(t) ++ Set(x) && redNodesHaveBlackChildren(res))
  
  def balance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    Node(c,a,x,b) match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(c,a,xV,b) => Node(c,a,xV,b)
    }
  } ensuring (res => content(res) == content(Node(c,a,x,b)))

  def buggyBalance(c: Color, a: Tree, x: Int, b: Tree): Tree = {
    Node(c,a,x,b) match {
      case Node(Black(),Node(Red(),Node(Red(),a,xV,b),yV,c),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),Node(Red(),a,xV,Node(Red(),b,yV,c)),zV,d) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),Node(Red(),b,yV,c),zV,d)) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
      case Node(Black(),a,xV,Node(Red(),b,yV,Node(Red(),c,zV,d))) => 
        Node(Red(),Node(Black(),a,xV,b),yV,Node(Black(),c,zV,d))
    }
  } ensuring (res => content(res) == content(Node(c,a,x,b)))
}
  """.trim)

  newExample("Search Linked-List", """
import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object SearchLinkedList {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def contains(list : List, elem : Int) : Boolean = (list match {
    case Nil() => false
    case Cons(x, xs) => x == elem || contains(xs, elem)
  })

  def firstZero(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(x, xs) => if (x == 0) 0 else firstZero(xs) + 1
  }) ensuring (res =>
    res >= 0 && (if (contains(list, 0)) {
      firstZeroAtPos(list, res)
    } else {
      res == size(list)
    }))

  def firstZeroAtPos(list : List, pos : Int) : Boolean = {
    list match {
      case Nil() => false
      case Cons(x, xs) => if (pos == 0) x == 0 else x != 0 && firstZeroAtPos(xs, pos - 1)
    }
  } 

  def goal(list : List, i : Int) : Boolean = {
    if(firstZero(list) == i) {
      if(contains(list, 0)) {
        firstZeroAtPos(list, i)
      } else {
        i == size(list)
      }
    } else {
      true
    }
  } holds
}
  """.trim)

  newExample("Sum and Max", """
import leon.Utils._
import leon.Annotations._

object SumAndMax {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def max(list : List) : Int = {
    require(list != Nil())
    list match {
      case Cons(x, Nil()) => x
      case Cons(x, xs) => {
        val m2 = max(xs)
        if(m2 > x) m2 else x
      }
    }
  }

  def sum(list : List) : Int = list match {
    case Nil() => 0
    case Cons(x, xs) => x + sum(xs)
  }

  def size(list : List) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def allPos(list : List) : Boolean = list match {
    case Nil() => true
    case Cons(x, xs) => x >= 0 && allPos(xs)
  }

  def prop0(list : List) : Boolean = {
    require(list != Nil())
    !allPos(list) || max(list) >= 0
  } holds

  @induct
  def property(list : List) : Boolean = {
    // This precondition was given in the problem but isn't actually useful :D
    // require(allPos(list))
    sum(list) <= size(list) * (if(list == Nil()) 0 else max(list))
  } holds
}
  """.trim)
}
