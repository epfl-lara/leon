import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._

//TODO: need to automatically check monotonicity of isConcrete
object RealTimeQueue {

  /**
   * A stream of values of type T
   */
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
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: $[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def ssize[T](l: $[Stream[T]]): BigInt = (l*).size

  //@monotonic
  def isConcrete[T](l: $[Stream[T]]): Boolean = {
    l.isEvaluated && (l* match {
      case SCons(_, tail) =>
        isConcrete(tail)
      case _ => true
    })
  }

   @invstate
  def rotate[T](f: $[Stream[T]], r: List[T], a: $[Stream[T]]): Stream[T] = { // doesn't change state
    require(r.size == ssize(f) + 1 && isConcrete(f))
    (f.value, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, a)
      case (SCons(x, tail), Cons(y, r1)) =>
        val newa: Stream[T] = SCons[T](y, a)
        val rot = $(rotate(tail, r1, newa)) //this creates a lazy rotate operation
        SCons[T](x, rot)
    }
  } ensuring (res => res.size == (f*).size + r.size + (a*).size && res.isCons && // using f*.size instead of ssize seems to speed up verification magically
                     time <= 30)

  def firstUnevaluated[T](l: $[Stream[T]]): $[Stream[T]] = {
    if (l.isEvaluated) {
      l* match {
        case SCons(_, tail) =>
          firstUnevaluated(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => (!(res*).isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    ((res*).isEmpty || !res.isEvaluated) && // if the return value is not a Nil closure then it would not have been evaluated
    (res.value match {
      case SCons(_, tail) =>
        firstUnevaluated(l) == firstUnevaluated(tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: $[Stream[T]], r: List[T], s: $[Stream[T]]) {
    def isEmpty = (f*).isEmpty
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(s)) &&
        ssize(s) == ssize(f) - r.size //invariant: |s| = |f| - |r|
    }
  }

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    val r = Cons[T](x, q.r)
    q.s.value match {
      case SCons(_, tail) =>
        Queue(q.f, r, tail)
      case SNil() =>
        val newa: Stream[T] = SNil[T]()
        val rotres = $(rotate(q.f, r, newa))
        Queue(rotres, Nil[T](), rotres)
    }
  } ensuring (res => res.valid && time <= 60)

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, nf) =>
        q.s.value match {
          case SCons(_, st) =>
            Queue(nf, q.r, st)
          case _ =>
            val newa: Stream[T] = SNil[T]()
            val rotres = $(rotate(nf, q.r, newa))
            Queue(rotres, Nil[T](), rotres)
        }
    }
  } ensuring(res => res.valid && time <= 120)
}
