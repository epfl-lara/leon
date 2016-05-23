package withOrb

import leon._
import lazyeval._
import lang._
import annotation._
import collection._
import instrumentation._
import invariant._

object RealTimeQueue {

  sealed abstract class Stream[T] {
    def isEmpty: Boolean = {
      this match {
        case SNil() => true
        case _      => false
      }
    }

    def isCons: Boolean = {
      this match {
        case SCons(_, _) => true
        case _           => false
      }
    }

    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + (t*).size
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: Lazy[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def isConcrete[T](l: Lazy[Stream[T]]): Boolean = {
    l.isEvaluated && (l* match {
      case SCons(_, tail) =>
        isConcrete(tail)
      case _ => true
    })
  }

  @invisibleBody
  @invstate
  def rotate[T](f: Lazy[Stream[T]], r: List[T], a: Lazy[Stream[T]]): Stream[T] = { // doesn't change state
    require(r.size == (f*).size + 1 && isConcrete(f))
    (f.value, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, a)
      case (SCons(x, tail), Cons(y, r1)) =>
        val newa: Stream[T] = SCons[T](y, a)
        val rot = $(rotate(tail, r1, newa)) //this creates a lazy rotate operation
        SCons[T](x, rot)
    }
  } ensuring (res => res.size == (f*).size + r.size + (a*).size && res.isCons &&
    time <= ?)

  /**
   * Returns the first element of the stream that is not evaluated.
   */
  def firstUnevaluated[T](l: Lazy[Stream[T]]): Lazy[Stream[T]] = {
    if (l.isEvaluated) {
      l* match {
        case SCons(_, tail) =>
          firstUnevaluated(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => (!(res*).isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    (res.value match {
      case SCons(_, tail) =>
        firstUnevaluated(l) == firstUnevaluated(tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]]) {
    def isEmpty = (f*).isEmpty
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(s)) &&
        (s*).size == (f*).size - r.size //invariant: |s| = |f| - |r|
    }
  }

  @inline
  def createQ[T](f: Lazy[Stream[T]], r: List[T], s: Lazy[Stream[T]]) = {
    s.value match {
      case SCons(_, tail) => Queue(f, r, tail)
      case SNil() =>
        val newa: Stream[T] = SNil()
        val rotres = $(rotate(f, r, newa))
        Queue(rotres, Nil(), rotres)
    }
  }

  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  }

  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, _) => x
    }
  } //ensuring (res => res.valid && time <= ?)

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    createQ(q.f, Cons(x, q.r), q.s)
  } ensuring (res => res.valid && time <= ?)

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, nf) =>
        createQ(nf, q.r, q.s)
    }
  } ensuring (res => res.valid && time <= ?)

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
