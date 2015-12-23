import leon.lazyeval._
import leon.lazyeval.$._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.math._

//TODO: need to automatically check monotonicity of isConcrete
/**
 * Here, both front and rear streans are scheduled
 */
object RealTimeDeque {

  /*def min(x: BigInt, y: BigInt) = if(x <= y) x else y
  def max(x: BigInt, y: BigInt) = if(x >= y) x else y*/

  /**
   * A stream of values of type T
   */
  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = {
      this match {
        case SNil() => true
        case _      => false
      }
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
        case SCons(x, t) => 1 + (t*).size
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: $[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  @inline
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
  def revAppend[T](l1: $[Stream[T]], l2: $[Stream[T]]): $[Stream[T]] = {
    require(isConcrete(l1) && isConcrete(l2))
    l1.value match {
      case SNil() => l2
      case SCons(x, tail) =>
        val nt: $[Stream[T]] = SCons[T](x, l2)
        revAppend(tail, nt)
    }
  } ensuring(res => ssize(res) == ssize(l1) + ssize(l2) &&
      isConcrete(res) &&
      (ssize(l1) >= 1 ==> (res*).isCons) &&
      time <= 20*ssize(l1) + 20)
      // takes O(|l1|) time

  @invstate
  def drop[T](n: BigInt, l: $[Stream[T]]): $[Stream[T]] = {
    require(n >= 0 && isConcrete(l) && ssize(l) >= n)
    if (n == 0) {
      l
    } else {
      l.value match {
        case SNil()         => l
        case SCons(x, tail) => drop(n - 1, tail)
      }
    }
  } ensuring(res => isConcrete(res) &&
      ssize(res) == ssize(l) - n &&
      time <= 20*n + 20)
  // takes O(n) time

  @invstate
  def take[T](n: BigInt, l: $[Stream[T]]): $[Stream[T]] = {
    require(n >= 0 && isConcrete(l) && ssize(l) >= n)
    val r: $[Stream[T]] =
      if (n == 0) {
        SNil[T]()
      } else {
        l.value match {
          case SNil() => l
          case SCons(x, tail) =>
            SCons[T](x, take(n - 1, tail))
        }
      }
    r
  } ensuring(res => isConcrete(res) &&
      ssize(res) == n &&
      time <= 30*n + 30)
  // takes O(n) time

  @invstate
  def takeLazy[T](n: BigInt, l: $[Stream[T]]): Stream[T] = {
    require(isConcrete(l) && n >= 1 && ssize(l) >= n)
    l.value match {
      case SCons(x, tail) =>
        if (n == 1)
          SCons[T](x, SNil[T]())
        else
          SCons[T](x, $(takeLazy(n - 1, tail)))
    }
  } ensuring(res => res.size == n && res.isCons &&
      time <= 20
      ) // takes O(1) time

  // requires unfoldFactor=2 why ?
  @invstate
  def rotateRev[T](r: $[Stream[T]], f: $[Stream[T]], a: $[Stream[T]]): Stream[T] = { // doesn't change state
    require(isConcrete(r) && isConcrete(f) && isConcrete(a) &&
      {
        val lenf = ssize(f)
        val lenr = ssize(r)
        (lenf <= 2 * lenr + 3 && lenf >= 2 * lenr + 1) // size invariant betwen 'f' and 'r'
      })
    r.value match {
      case SNil() => revAppend(f, a).value // |f| <= 3
      case SCons(x, rt) =>
        SCons(x, $(rotateRev(rt, drop(2, f), revAppend(take(2, f), a)))) // here we are creating a lazy closure
    }  // here, it doesn't matter whether 'f' has i elements or not, what we want is |drop(2,f)| + |take(2,f)| == |f|
  } ensuring (res => res.size == (r*).size + (f*).size + (a*).size &&
      res.isCons &&
      time <= 250)
  //takes constant time

  @invstate
  def rotateDrop[T](r: $[Stream[T]], i: BigInt, f: $[Stream[T]]): Stream[T] = {
    require(isConcrete(r) && isConcrete(f) && i >= 0 && {
      val lenf = ssize(f)
      val lenr = ssize(r)
      (lenf >= 2 * lenr + 2 && lenf <= 2 * lenr + 3) && // size invariant between 'f' and 'r'
      lenf > i
    })

    val rval = r.value
    if(i < 2 || rval == SNil[T]()) {
      val a: $[Stream[T]] = SNil[T]()
      rotateRev(r, drop(i, f), a)
    } else {
      rval match {
        case SCons(x, rt) =>
          SCons(x, $(rotateDrop(rt, i - 2, drop(2, f))))
      }
    }
  } ensuring(res => res.size == (r*).size + (f*).size - i &&
      res.isCons &&
      time <= 300)
  // takes constant time

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
    ((res*).isEmpty || !res.isEvaluated)
    && // if the return value is not a Nil closure then it would not have been evaluated
    (res.value match {
      case SCons(_, tail) =>
        firstUnevaluated(l) == firstUnevaluated(tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: $[Stream[T]], lenf: BigInt, sf: $[Stream[T]],
      r: $[Stream[T]], lenr: BigInt, sr: $[Stream[T]]) {
    def isEmpty = lenf + lenr == 0
    def valid = {
      (firstUnevaluated(f) == firstUnevaluated(sf)) &&
        (firstUnevaluated(r) == firstUnevaluated(sr)) &&
        (lenf == ssize(f) && lenr == ssize(r)) &&
        (lenf <= 2*lenr + 1 && lenr <= 2*lenf + 1) &&
        {
          val mind = min(2*lenr-lenf+2, 2*lenf-lenr+2)
          ssize(sf) <= mind && ssize(sr) <= mind
        }
    }
  }

  def createQueue[T](f: $[Stream[T]], lenf: BigInt, sf: $[Stream[T]],
      r: $[Stream[T]], lenr: BigInt, sr: $[Stream[T]]): Queue[T] = {
    require(firstUnevaluated(f) == firstUnevaluated(sf) &&
        firstUnevaluated(r) == firstUnevaluated(sr) &&
        (lenf == ssize(f) && lenr == ssize(r)) &&
        ((lenf - 1 <= 2*lenr + 1 && lenr <= 2*lenf + 1) ||
          (lenf <= 2*lenr + 1 && lenr - 2 <= 2*lenf + 1)) &&
        {
          val mind = max(min(2*lenr-lenf+2, 2*lenf-lenr+2), 0)
          ssize(sf) <= mind && ssize(sr) <= mind
        })
    if(lenf > 2*lenr + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nr = rotateDrop(r, i, f)
      val nf = takeLazy(i, f)
      Queue(nf, i, nf, nr, j, nr)
    } else if(lenr > 2*lenf + 1) {
      val i = (lenf + lenr) / 2
      val j = lenf + lenr - i
      val nf =  rotateDrop(f, j, r) // here, both 'r' and 'f' are concretized
      val nr = takeLazy(j, r)
      Queue(nf, i, nf, nr, j, nr)
    } else
      Queue(f, lenf, sf, r, lenr, sr)
  } ensuring(res => res.valid &&
      time <= 400)

  def check[T](l: $[Stream[T]]): Boolean = {
    l.isEvaluated
  }

  def funeCompose[T](l1: $[Stream[T]], st1: Set[$[Stream[T]]], st2: Set[$[Stream[T]]]): Boolean = {
    require(st1.subsetOf(st2))
    (if (check(l1) withState st1) {
      l1* match {
        case SCons(_, tail) =>
          funeCompose(tail, st1, st2)
        case _ => true
      }
    } else true) &&
      (firstUnevaluated(l1) withState st2) == (firstUnevaluated(firstUnevaluated(l1) withState st1) withState st2)
  } holds

  def funeMonotone[T](l1: $[Stream[T]], l2: $[Stream[T]], st1: Set[$[Stream[T]]], st2: Set[$[Stream[T]]]): Boolean = {
    require((firstUnevaluated(l1) withState st1) == (firstUnevaluated(l2) withState st1) &&
        st1.subsetOf(st2))
     funeCompose(l1, st1, st2) &&
     funeCompose(l2, st1, st2) &&
    (if (check(l1) withState st1) {
      l1* match {
        case SCons(_, tail) =>
          funeMonotone(tail, l2, st1, st2)
        case _ => true
      }
    } else true) &&
      (firstUnevaluated(l1) withState st2) == (firstUnevaluated(l2) withState st2)
  } holds

  def forceSched[T](f: $[Stream[T]], sf: $[Stream[T]], r: $[Stream[T]], sr: $[Stream[T]], front: Boolean): $[Stream[T]] = {
    require(firstUnevaluated(f) == firstUnevaluated(sf) &&
        firstUnevaluated(r) == firstUnevaluated(sr))
    if (front) {
      sf.value match {
        case SCons(_, tail) => tail
        case _              => sf
      }
    } else {
      sr.value match {
        case SCons(_, tail) => tail
        case _              => sr
      }
    }
  } ensuring(res => {
    //lemma instantiations
    val in = $.inState[Stream[T]]
    val out = $.outState[Stream[T]]
    funeMonotone(r, sr, in, out) &&
      funeMonotone(f, sf, in, out) && {
       val funef = firstUnevaluated(f)
       val funeres = firstUnevaluated(res)
       val funer = firstUnevaluated(r)
       val funesr = firstUnevaluated(sr)
       val funesf = firstUnevaluated(sf)
       val rsize = ssize(res)
      (if (front) {
         funef == funeres && // follows from post of fune
           funer == funesr &&
           (rsize == 0 || rsize == ssize(sf) - 1)
      } else {
        funer == funeres && // follows from post of fune
          funef == funesf &&
          (rsize == 0 || rsize == ssize(sr) - 1)
      })
    } && time <= 350
  })

  def forceSchedsTwice[T](q: Queue[T]): ($[Stream[T]], $[Stream[T]]) = {
    require(q.valid)
    val nsf = forceSched(q.f,
      forceSched(q.f, q.sf, q.r, q.sr, true),
      q.r, q.sr, true)
    val nsr = forceSched(q.f, nsf, q.r,
      forceSched(q.f, nsf, q.r, q.sr, false), false)
    (nsf, nsr)

  } ensuring (res => {
    val nsf = res._1
    val nsr = res._2
    val funef = firstUnevaluated(q.f)
    val funesf = firstUnevaluated(nsf)
    val funer = firstUnevaluated(q.r)
    val funesr = firstUnevaluated(nsr)
    funef == funesf && funer == funesr &&
      (ssize(nsf) == 0 || ssize(nsf) == ssize(q.sf) - 2) &&
      (ssize(nsr) == 0 || ssize(nsr) == ssize(q.sr) - 2) &&
    time <= 1500
  })

  def empty[T] = {
    val nil: $[Stream[T]] = SNil[T]()
    Queue(nil, 0, nil, nil, 0, nil)
  }

  /**
   * Adding an element to the front of the list
   */
  def cons[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    val nf: Stream[T] = SCons[T](x, q.f)
    // force the front and rear scheds once
    val nsf = forceSched(q.f, q.sf, q.r, q.sr, true)
    val nsr = forceSched(q.f, nsf, q.r, q.sr, false)
    createQueue(nf, q.lenf + 1, nsf, q.r, q.lenr, nsr)
  } ensuring (res => res.valid && time <= 1200)

  /**
   * Removing the a element from front, and returning the tail
   */
  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    forceF(q) match {
      case _ =>
        tailSub(q)
    }
  } ensuring(res => res.valid && time <= 3000)

  def forceF[T](q: Queue[T]) = {
    require(q.valid)
    q.f.value
  } ensuring {_ =>
    //lemma instantiations
    val in = $.inState[Stream[T]]
    val out = $.outState[Stream[T]]
    funeMonotone(q.r, q.sr, in, out) &&
      funeMonotone(q.f, q.sf, in, out) &&
      q.valid
  }

  def tailSub[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid && q.f.isEvaluated)
    q.f.value match {
      case SCons(x, nf) =>
        val (nsf, nsr) = forceSchedsTwice(q)
        // here, sf and sr got smaller by 2 holds, the schedule invariant still holds
        createQueue(nf, q.lenf - 1, nsf, q.r, q.lenr, nsr)
      case SNil() =>
         // in this case 'r' will have only one element by invariant
        empty[T]
    }
  } ensuring(res => res.valid && time <= 2750)

  def reverse[T](q: Queue[T]): Queue[T] = {
    require(q.valid)
    Queue(q.r, q.lenr, q.sr, q.f, q.lenf, q.sf)
  } ensuring(q.valid && time <= 10)

}
