import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._

//TODO: need to automatically check monotonicity of isConcrete
object RealTimeQueue {

  sealed abstract class LList[T] {
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
  case class SCons[T](x: T, tail: $[LList[T]]) extends LList[T]
  case class SNil[T]() extends LList[T]

  def ssize[T](l: $[LList[T]]): BigInt = (l*).size

  //@monotonic
  def isConcrete[T](l: $[LList[T]]): Boolean = {
    (l.isEvaluated && (l* match {
      case SCons(_, tail) =>
        isConcrete(tail)
      case _ => true
    })) || (l*).isEmpty
  }

   @invstate
  def rotate[T](f: $[LList[T]], r: List[T], a: $[LList[T]]): LList[T] = {
    require(r.size == ssize(f) + 1 && isConcrete(f)) // size invariant between 'f' and 'r' holds
    (f.value, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, a)
      case (SCons(x, tail), Cons(y, r1)) =>
        val newa: LList[T] = SCons[T](y, a)
        val rot = $(rotate(tail, r1, newa)) //this creates a lazy rotate operation
        SCons[T](x, rot)
    }
  } ensuring (res => res.size == (f*).size + r.size + (a*).size && res.isCons && // using f*.size instead of ssize seems to help magically
                     time <= 30)

  def firstUnevaluated[T](l: $[LList[T]]): $[LList[T]] = {
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

  def streamScheduleProperty[T](s: $[LList[T]], sch: $[LList[T]]) = {
    firstUnevaluated(s) == firstUnevaluated(sch)
  }

  case class Queue[T](f: $[LList[T]], r: List[T], s: $[LList[T]]) {
    def isEmpty = (f*).isEmpty
    def valid = {
      streamScheduleProperty(f, s) &&
        ssize(s) == ssize(f) - r.size //invariant: |s| = |f| - |r|
    }
  }

  def createQueue[T](f: $[LList[T]], r: List[T], sch: $[LList[T]]): Queue[T] = {
    require(streamScheduleProperty(f, sch) &&
      ssize(sch) == ssize(f) - r.size + 1) //size invariant holds
    sch.value match { // evaluate the schedule if it is not evaluated
      case SCons(_, tail) =>
        Queue(f, r, tail)
      case SNil() =>
        val newa: LList[T] = SNil[T]()
        val rotres = $(rotate(f, r, newa))
        Queue(rotres, Nil[T](), rotres)
    }
  } ensuring (res => res.valid && time <= 50)

  def enqueue[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    createQueue(q.f, Cons[T](x, q.r), q.s)
  } ensuring (res => res.valid && time <= 60)

  def dequeue[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    q.f.value match {
      case SCons(x, nf) =>
        q.s.value match {
          case SCons(_, st) => //here, the precondition of createQueue (reg. suffix property) may get violated, so it is handled specially here.
            Queue(nf, q.r, st)
          case _ =>
            val newa: LList[T] = SNil[T]()
            val rotres = $(rotate(nf, q.r, newa))
            Queue(rotres, Nil[T](), rotres)
        }
    }
  } ensuring(res => res.valid && time <= 120)
}
