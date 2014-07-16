// reverse is not implemented tail-recursively! :(

// Problems : content

import leon.lang._
import leon.annotation._

object AmortizedQueue {
  sealed abstract class List {
    val size : Int = (this match {
      case Nil() => 0
      case Cons(_, xs) => 1 + xs.size
    }) ensuring(_ >= 0)
  }
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

 

  def content(l: List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def q2l(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def nth(l:List, n:Int) : Int = {
    require(0 <= n && n < l.size)
    l match {
      case Cons(x,xs) =>
    if (n==0) x else nth(xs, n-1)
    }
  }

  def l2mFrom(k:Int, l:List) : Map[Int,Int] = (l match {
    case Nil() => Map[Int,Int]()
    case Cons(x,xs) => l2mFrom(k+1,xs).updated(k,x)
  })

  def l2m(l:List) : Map[Int,Int] = l2mFrom(0,l)

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => res.size == l1.size + l2.size  && content(res) == content(l1) ++ content(l2))

  def concatTest(l1 : List, l2 : List, i:Int) : List = ({
    require(0 <= i && i < l1.size + l2.size)
    l1 match {
      case Nil() => l2
      case Cons(x,xs) => Cons(x,
                  if (i == 0) concat(xs, l2)
                  else concatTest(xs, l2, i-1))
    }
  }) ensuring (res => res.size == l1.size + l2.size &&
           content(res) == content(l1) ++ content(l2) &&
           nth(res,i) == (if (i < l1.size) nth(l1,i) else nth(l2,i-l1.size)) &&
           res == concat(l1,l2))

  def nthConcat(l1:List, l2:List, i:Int) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    concatTest(l1, l2, i) == concatTest(l1, l2, i) &&
    nth(concat(l1,l2), i) == (if (i < l1.size) nth(l1,i) else nth(l2,i-l1.size))
  } holds

  def sameUpto(l1:List, l2:List, k:Int) : Boolean = {
    require(0 <= k)
    (l1,l2) match {
      case (Nil(),Nil()) => true
      case (Nil(),_) => false
      case (_,Nil()) => false
      case (Cons(x,xs),Cons(y,ys)) => {
    x==y && (if (k==0) true else sameUpto(xs,ys,k-1))
      }
    }
  } ensuring(res => !(l1.size==k && l2.size==k && res) || l1==l2)

  @induct
  def concatAssoc(l1:List, l2:List, l3:List) : Boolean = {
    concat(l1, concat(l2,l3)) == concat(concat(l1,l2), l3)
  } holds

  def concatCons(x:Int, l2:List, l3:List) : Boolean = {
    Cons(x, concat(l2,l3)) == concat(Cons(x,l2), l3)
  } holds

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => front.size >= rear.size
  }

  def rev1(l : List, acc: List) : List = { l match {
    case Nil() => acc
    case Cons(x,xs) => rev1(xs, Cons(x,acc))
  }} ensuring { res => res.size == l.size + acc.size && content(res) == content(l) ++ content(acc) }

  def reverse(l : List) : List = { rev1(l, Nil()) 
  } ensuring (res => content(res) == content(l) && res.size == l.size)

  def revConcatNth(l1:List, l2:List, i:Int) : Boolean = {
    require(0 <= i && i < l1.size+l2.size)
    nth(reverse(concat(l1,l2)),i) == nth(concat(reverse(l2), reverse(l1)),i)
  } holds

  def revrev(l:List) : Boolean = {
    reverse(reverse(l)) == l
  } holds

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (rear.size <= front.size)
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil())
  } ensuring(res => isAmortized(res) && q2l(Queue(front, rear)) == q2l(res))

  def isEmpty(queue : AbsQueue) : Boolean = (queue match {
      case Queue(Nil(), Nil()) => true
      case _ => false
  }) ensuring(res => (res == (q2l(queue) == Nil())))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(res => isAmortized(res) && q2l(res) == concat(q2l(queue), Cons(elem, Nil())))
    // this did not find a counterexample:
    // ensuring(res => isAmortized(res) && q2l(res) == Cons(elem, q2l(queue)))

  def push(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(Cons(elem,front), rear)
  }) ensuring(res => isAmortized(res) && q2l(res) == Cons(elem, q2l(queue)))


 // I did not know why this does not type check
  def matchQ(queue : AbsQueue) : (Int, AbsQueue) = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => (f, amortizedQueue(fs, rear))
    }
  }) ensuring(res => {
    val (f,q) = res
    q2l(queue) == Cons(f, q2l(q))
  })

  def tail(queue : AbsQueue) : AbsQueue = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  }) ensuring(res => isAmortized(res) && (q2l(queue) match {
    case Nil() => false
    case Cons(_,xs) => q2l(res)==xs
  }))

  def front(queue : AbsQueue) : Int = ({
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }) ensuring(res => q2l(queue) match {
    case Nil() => false
    case Cons(x,_) => x==res
  })

  // @induct
  // def propEnqueue(rear : List, front : List, list : List, elem : Int) : Boolean = {
  //   require(isAmortized(Queue(front, rear)))
  //   val queue = Queue(front, rear)
  //   if (q2l(queue) == list) {
  //     q2l(enqueue(queue, elem)) == concat(list, Cons(elem, Nil()))
  //   } else
  //     true
  // } holds

  @induct
  def propFront(queue : AbsQueue, list : List, elem : Int) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (q2l(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  } holds

  @induct
  def propTail(rear : List, front : List, list : List, elem : Int) : Boolean = {
    require(!isEmpty(Queue(front, rear)) && isAmortized(Queue(front, rear)))
    if (q2l(Queue(front, rear)) == list) {
      list match {
        case Cons(_, xs) => q2l(tail(Queue(front, rear))) == xs
      }
    } else
      true
  } // holds

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
  
  def emptyQueue() : AbsQueue = Queue(Nil(), Nil())

/*  // pseudorandom els. to insert
  def psr (input : Int) : Int = {
    (input * 476272 + 938709) % 187987
  }
  def rec(size : Int, acc : AbsQueue) : AbsQueue = {
    if (size == 0) acc
    else rec(size -1, enqueue(acc, psr(size)))
  }
  
  def test(size : Int) : AbsQueue = { 
      rec(size, emptyQueue)
  }
*/
  def test(q:AbsQueue, i:Int) : AbsQueue = enqueue(q,i)
  def init() : AbsQueue = emptyQueue()

}
