package realtimequeue

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._

object RealTimeQueue {

  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = this == SNil[T]()

    lazy val tail: Stream[T] = {
      require(!isEmpty)
      this match {
        case SCons(_, tailFun, _) => tailFun()
      }
    }

    def size = this match {
      case SCons(_, _, r) => r
      case SNil()         => BigInt(0)
    }

    /**
     * A property that is true if `sz` field decreases for the tail of the stream.
     * `sz` is a well-founded ordering.
     */
    def valid: Boolean = {
      this match {
        case c @ SCons(_, _, _) =>
          val s = size
          s > 0 && s == (c.tail*).size + 1 && (c.tail*).valid
        case _ => true
      }
    }
  }
  private case class SCons[T](x: T, tailFun: () => Stream[T], sz: BigInt) extends Stream[T]
  private case class SNil[T]() extends Stream[T]

  /**
   * A property that holds for stream where all elements have been memoized.
   */
  def isConcrete[T](l: Stream[T]): Boolean = {
    require(l.valid)
    l match {
      case c @ SCons(_, _, _) =>
        cached(c.tail) && isConcrete(c.tail*)
      case _ => true
    }
  }

  sealed abstract class List[T] {
    val size: BigInt = {
      this match {
        case Nil()      => BigInt(0)
        case Cons(_, t) => 1 + t.size
      }
    } ensuring (_ >= 0)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

  /**
   * A function that lazily performs an operation equivalent to `f ++ reverse(r) ++ a`.
   * Based on the implementation provided in Pg. of Functional Data Structures by Okasaki.
   */
  @invisibleBody
  @invstate
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): Stream[T] = {
    require(r.size == f.size + 1 && f.valid && a.valid && isConcrete(f))
    (f, r) match {
      case (SNil(), Cons(y, _)) => // Here, 'y' is the only element in 'r'
        SCons[T](y, lift(a), a.size + 1) //  size: a.size + 1
      case (c @ SCons(x, _, _), Cons(y, r1)) =>
        val newa = SCons[T](y, lift(a), a.size + 1) // size: a.size + 1
        val ftail = c.tail
        val rot = () => rotate(ftail, r1, newa)
        SCons[T](x, rot, f.size + r.size + a.size) // size: f.size + r.size + a.size
    }
  } ensuring (res => res.valid &&
    res.size == f.size + r.size + a.size &&
    !res.isEmpty && steps <= ?)

  /**
   * Returns the first element of the stream whose tail is not memoized.
   */
  def firstUneval[T](l: Stream[T]): Stream[T] = {
    require(l.valid)
    l match {
      case c @ SCons(_, _, _) =>
        if (cached(c.tail))
          firstUneval(c.tail*)
        else l
      case _ => l
    }
  } ensuring (res =>
    // (a) the returned stream is valid
    res.valid &&
    // (b) if there are no lazy closures then the stream is concrete
    (!res.isEmpty || isConcrete(l)) &&
    /* (c) after evaluating the firstUneval closure in 'l'
     we can access the next unevaluated closure */
    (res match {
      case c @ SCons(_, _, _) =>
        firstUneval(l) == firstUneval(c.tail)
      case _ => true
    }))

  case class Queue[T](f: Stream[T], r: List[T], s: Stream[T]) {
    @inline
    def isEmpty = f.isEmpty

    def valid = {
      f.valid && s.valid &&
      // invariant: firstUneval of `f` and `s` are the same.
      (firstUneval(f) == firstUneval(s)) &&
      s.size == f.size - r.size // invariant: |s| = |f| - |r|
    }
  }

  /**
   * A helper function for enqueue and dequeue methods that forces
   * the schedule once
   */
  @inline
  def createQ[T](f: Stream[T], r: List[T], s: Stream[T]) = {
    s match {
      case c @ SCons(_, _, _) => Queue(f, r, c.tail) // force the schedule once
      case SNil() =>
        val rotres = rotate(f, r, SNil[T]())
        Queue(rotres, Nil(), rotres)
    }
  }

  /**
   * Creates an empty queue, with an empty schedule
   */
  def empty[T] = {
    val a: Stream[T] = SNil()
    Queue(a, Nil(), a)
  } ensuring (res => res.valid && steps <= ?)

  /**
   * Reads the first elements of the queue without removing it.
   */
  def head[T](q: Queue[T]): T = {
    require(!q.isEmpty && q.valid)
    q.f match {
      case SCons(x, _, _) => x
    }
  } ensuring (res => steps <= ?)

  /**
   * Appends an element to the end of the queue
   */
  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    createQ(q.f, Cons(x, q.r), q.s)
  } ensuring { res =>
    funeMonotone(q.f, q.s, inSt[T], outSt[T]) &&
      res.valid && steps <= ?
  }

  /**
   * Removes the element at the beginning of the queue
   */
  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f match {
      case c @ SCons(x, _, _) =>
        createQ(c.tail, q.r, q.s)
    }
  } ensuring { res =>
    funeMonotone(q.f, q.s, inSt[T], outSt[T]) &&
      res.valid && steps <= ?
  }

  // Properties of `firstUneval`. We use `fune` as a shorthand for `firstUneval`
  /**
   * Lemma: st1.subsetOf(st2) ==> fune(l, st2) == fune(fune(l, st1), st2)
   */
  @traceInduct
  def funeCompose[T](l1: Stream[T], st1: Set[Fun[T]], st2: Set[Fun[T]]): Boolean = {
    require(st1.subsetOf(st2) && l1.valid)
    (firstUneval(l1) in st2) == (firstUneval(firstUneval(l1) in st1) in st2)
  } holds

  /**
   * Lemma: monotonicity of `fistUneval` function with respect to the state.
   */
  @invisibleBody
  def funeMonotone[T](l1: Stream[T], l2: Stream[T], st1: Set[Fun[T]], st2: Set[Fun[T]]): Boolean = {
    require(l1.valid && l2.valid && (firstUneval(l1) in st1) == (firstUneval(l2) in st1) &&
      st1.subsetOf(st2))
    funeCompose(l1, st1, st2) && // implies: fune(l1, st2) == fune(fune(l1,st1), st2)
      funeCompose(l2, st1, st2) && // implies: fune(l2, st2) == fune(fune(l2,st1), st2)
      (firstUneval(l1) in st2) == (firstUneval(l2) in st2) // property
  } holds
}
