package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import invariant._

/**
 * Requires unrollfactor=2
 */
object RealTimeQueue {

  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = this == SNil[T]()
    @inline
    def isCons: Boolean = !isEmpty

    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case c@SCons(_, _) => 1 + (c.tail*).size
      }
    } ensuring (_ >= 0)

    lazy val tail: Stream[T] = {
      require(isCons)
      this match {
        case SCons(x, tailFun) => tailFun()
      }
    }
  }
  // wellfoundedness prop: (tailFun*).rank < this.rank && \forall x. rank >= 0 && tailFun*.satisfies prop
  private case class SCons[T](x: T, tailFun: () => Stream[T]) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  def isConcrete[T](l: Stream[T]): Boolean = {
    l match {
      case c@SCons(_, _) =>
        cached(c.tail) && isConcrete(c.tail*)
      case _ => true
    }
  }

  @invisibleBody
  @invstate // says that the function doesn't change state
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): Stream[T] = {
    require(r.size == f.size + 1 && isConcrete(f))
    (f, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, lift(a)) //  rank: a.rank + 1
      case (c@SCons(x, _), Cons(y, r1)) =>
        val newa = SCons[T](y, lift(a)) // rank : a.rank + 1
        val ftail = c.tail
        val rot = () => rotate(ftail, r1, newa)
        SCons[T](x, rot) // @ rank == f.rank + r.rank + a.rank
    }
  } ensuring (res => res.size == f.size + r.size + a.size && res.isCons && steps <= ?) // Orb results: steps <= 31

  /**
   * Returns the first element of the stream whose tail is not evaluated.
   */
  // @invisibleBody
  def firstUnevaluated[T](l: Stream[T]): Stream[T] = {
    l match {
      case c @ SCons(_, _) =>
        if (cached(c.tail))
          firstUnevaluated(c.tail*)
        else l
      case _           => l
    }
  } ensuring (res => (!res.isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    (res match {
      case c@SCons(_, _) =>
        firstUnevaluated(l) == firstUnevaluated(c.tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    @inline
    def isEmpty = f.isEmpty

    //@inline
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(s)) &&
        s.size == f.size - r.size //invariant: |s| = |f| - |r|
    }
  }

  @inline
  def createQ[T](f: Stream[T], r: List[T], s: Stream[T]) = {
    s match {
      case c@SCons(_, _) => Queue(f, r, c.tail) // force the schedule once
      case SNil() =>
        val rotres = rotate(f, r, SNil[T]())
        Queue(rotres, Nil(), rotres)
    }
  }

  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    q.f match {
      case SCons(x, _) => x
    }
  } //ensuring (res => res.valid && steps <= ?)

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    createQ(q.f, Cons(x, q.r), q.s)
  } ensuring { res =>
    funeMonotone(q.f, q.s, inSt[T], outSt[T]) &&
    res.valid && steps <= ?
  } // Orb results: steps <= 62

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f match {
      case c@SCons(x, _) =>
        createQ(c.tail, q.r, q.s)
    }
  } ensuring{res =>
    funeMonotone(q.f, q.s, inSt[T], outSt[T]) &&
    res.valid && steps <= ?
  } // Orb results: steps <= 119

   // Properties of `firstUneval`. We use `fune` as a shorthand for `firstUneval`
  /**
   * st1.subsetOf(st2) ==> fune(l, st2) == fune(fune(l, st1), st2)
   */
  @traceInduct
  def funeCompose[T](l1: Stream[T], st1: Set[Fun[T]], st2: Set[Fun[T]]): Boolean = {
    require(st1.subsetOf(st2))
    // property
    (firstUnevaluated(l1) in st2) == (firstUnevaluated(firstUnevaluated(l1) in st1) in st2)
  } holds

  @invisibleBody
  def funeMonotone[T](l1: Stream[T], l2: Stream[T], st1: Set[Fun[T]], st2: Set[Fun[T]]): Boolean = {
    require((firstUnevaluated(l1) in st1) == (firstUnevaluated(l2) in st1) &&
        st1.subsetOf(st2))
     funeCompose(l1, st1, st2) &&  // implies: fune(l1, st2) == fune(fune(l1,st1), st2)
     funeCompose(l2, st1, st2) &&  // implies: fune(l2, st2) == fune(fune(l2,st1), st2)
      (firstUnevaluated(l1) in st2) == (firstUnevaluated(l2) in st2) // property
  } holds

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.AmortizedQueue
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._

    println("Running RTQ test...")
    val ops = 10000000
    val rand = Random
    // initialize to a queue with one element (required to satisfy preconditions of dequeue and front)
    var rtq = empty[BigInt]
    //var amq = AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil())
    var totalTime1 = 0L
    var totalTime2 = 0L
    println(s"Testing amortized emphemeral behavior on $ops operations...")
    for (i <- 0 until ops) {
      if (!rtq.isEmpty) {
        val h1 = head(rtq)
        //val h2 = amq.head
        //assert(h1 == h2, s"Eager head: $h2 Lazy head: $h1")
      }
      rand.nextInt(2) match {
        case x if x == 0 => //enqueue
          //          /if(i%100000 == 0) println("Enqueue..")
          rtq = timed { enqueue(BigInt(i), rtq) } { totalTime1 += _ }
        //amq = timed { amq.enqueue(BigInt(i)) } { totalTime2 += _ }
        case x if x == 1 => //dequeue
          if (!rtq.isEmpty) {
            //if(i%100000 == 0) println("Dequeue..")
            rtq = timed { dequeue(rtq) } { totalTime1 += _ }
            //amq = timed { amq.dequeue } { totalTime2 += _ }
          }
      }
    }
    println(s"Ephemeral Amortized Time - Eager: ${totalTime2 / 1000.0}s Lazy: ${totalTime1 / 1000.0}s") // this should be linear in length for both cases
    // now, test worst-case behavior (in persitent mode if necessary)
    val length = (1 << 22) - 2 // a number of the form: 2^{n-2}
    // reset the queues
    rtq = empty[BigInt]
    //amq = AmortizedQueue.Queue(AmortizedQueue.Nil(), AmortizedQueue.Nil())
    // enqueue length elements
    for (i <- 0 until length) {
      rtq = enqueue(BigInt(0), rtq)
      //amq = amq.enqueue(BigInt(0))
    }
    //println(s"Amortized queue size: ${amq.front.size}, ${amq.rear.size}")
    //dequeue 1 element from both queues
    //timed { amq.dequeue } { t => println(s"Time to dequeue one element from Amortized Queue in the worst case: ${t / 1000.0}s") }
    timed { dequeue(rtq) } { t => println(s"Time to dequeue one element from RTQ in the worst case: ${t / 1000.0}s") }
  }
}
