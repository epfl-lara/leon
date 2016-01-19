import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._

object RealTimeQueue {

  /**
   * A stream of values of type T
   */
  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = {
      this == SNil[T]()
    }

    @inline
    def isCons: Boolean = {
      this match {
        case SCons(_, _) => true
        case _           => false
      }
    }

    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: $[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def ssize[T](l: $[Stream[T]]): BigInt = (l*).size

  def isConcrete[T](l: $[Stream[T]]): Boolean = {
//    l.isEvaluated && (l* match {
//      case SCons(_, tail) =>
//        isConcrete(tail)
//      case _ => true
//    })
    (firstUneval(l)*) == SNil[T]()
  }

   @invstate
  def rotate[T](f: $[Stream[T]], r: List[T], a: $[Stream[T]]): Stream[T] = { // doesn't change state
    require(r.size == (f*).size + 1 && isConcrete(f))
    (f.value, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons(y, a)
      case (SCons(x, tail), Cons(y, r1)) =>
        val newa: Stream[T] = SCons(y, a)
        val rot = $(rotate(tail, r1, newa)) //this creates a lazy rotate operation
        SCons(x, rot)
    }
  } ensuring (res => res.size == (f*).size + r.size + (a*).size && res.isCons && // using f*.size instead of ssize seems to speed up verification magically
                     time <= 30)

  def firstUneval[T](l: $[Stream[T]]): $[Stream[T]] = {
    if (l.isEvaluated) {
      l* match {
        case SCons(_, tail) =>
          firstUneval(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => 
    (res.value match {
      case SCons(_, tail) =>
        firstUneval(l) == firstUneval(tail) // after evaluating the firstUneval closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: $[Stream[T]], r: List[T], s: $[Stream[T]]) {
    def isEmpty = (f*).isEmpty
    def valid = {
      (firstUneval(f) == firstUneval(s)) &&
        ssize(s) == ssize(f) - r.size //invariant: |s| = |f| - |r|
    }
  }
  
  @inline
  def createQ[T](f: $[Stream[T]], r: List[T], s: $[Stream[T]]) = {
    s.value match {
      case SCons(_, tail) => Queue(f, r, tail)
      case SNil() =>
        val newa: Stream[T] = SNil()
        val rotres = $(rotate(f, r, newa))
        Queue(rotres, Nil(), rotres)
    }
  }

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)    
    createQ(q.f, Cons(x, q.r), q.s)
  } ensuring (res => res.valid && time <= 60)

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, nf) =>
        createQ(nf, q.r, q.s)
    }
  } ensuring(res => res.valid && time <= 120)
}
