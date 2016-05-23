import leon._
import lazyeval._
import lang._
import annotation._
import collection._
import instrumentation._
import math._

/**
 * A constant time deque based on Okasaki's implementation: Fig.8.4 Pg. 112.
 * Here, both front and rear streams are scheduled.
 * We require both the front and the rear streams to be of almost equal
 * size. If not, we lazily rotate the streams.
 * The invariants are a lot more complex than in `RealTimeQueue`.
 * The program also fixes a bug in Okasaki's implementatin: see function `rotateDrop`
 */
object RealTimeDeque {

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
  case class SCons[T](x: T, tail: Lazy[Stream[T]]) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  @inline
  def ssize[T](l: Lazy[Stream[T]]): BigInt = (l*).size

  def isConcrete[T](l: Lazy[Stream[T]]): Boolean = {
    l.isEvaluated && (l* match {
      case SCons(_, tail) =>
        isConcrete(tail)
      case _ => true
    })
  }

  @invstate
  def revAppend[T](l1: Lazy[Stream[T]], l2: Lazy[Stream[T]]): Lazy[Stream[T]] = {
    require(isConcrete(l1) && isConcrete(l2))
    l1.value match {
      case SNil() => l2
      case SCons(x, tail) =>
        val nt: Lazy[Stream[T]] = SCons[T](x, l2)
        revAppend(tail, nt)
    }
  } ensuring(res => ssize(res) == ssize(l1) + ssize(l2) &&
      isConcrete(res) &&
      (ssize(l1) >= 1 ==> (res*).isCons) &&
      time <= 20*ssize(l1) + 20)

  @invstate
  def drop[T](n: BigInt, l: Lazy[Stream[T]]): Lazy[Stream[T]] = {
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

  @invstate
  def take[T](n: BigInt, l: Lazy[Stream[T]]): Lazy[Stream[T]] = {
    require(n >= 0 && isConcrete(l) && ssize(l) >= n)
    val r: Lazy[Stream[T]] =
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

  @invstate
  def takeLazy[T](n: BigInt, l: Lazy[Stream[T]]): Stream[T] = {
    require(isConcrete(l) && n >= 1 && ssize(l) >= n)
    l.value match {
      case SCons(x, tail) =>
        if (n == 1)
          SCons[T](x, SNil[T]())
        else
          SCons[T](x, $(takeLazy(n - 1, tail)))
    }
  } ensuring(res => res.size == n && res.isCons &&
      time <= 20)

  @invstate
  def rotateRev[T](r: Lazy[Stream[T]], f: Lazy[Stream[T]], a: Lazy[Stream[T]]): Stream[T] = {
    require(isConcrete(r) && isConcrete(f) && isConcrete(a) &&
      {
        val lenf = ssize(f)
        val lenr = ssize(r)
        (lenf <= 2 * lenr + 3 && lenf >= 2 * lenr + 1)
      })
    r.value match {
      case SNil() => revAppend(f, a).value // |f| <= 3
      case SCons(x, rt) =>
        SCons(x, $(rotateRev(rt, drop(2, f), revAppend(take(2, f), a))))
    }  // here, it doesn't matter whether 'f' has i elements or not, what we want is |drop(2,f)| + |take(2,f)| == |f|
  } ensuring (res => res.size == (r*).size + (f*).size + (a*).size &&
      res.isCons &&
      time <= 250)

  @invstate
  def rotateDrop[T](r: Lazy[Stream[T]], i: BigInt, f: Lazy[Stream[T]]): Stream[T] = {
    require(isConcrete(r) && isConcrete(f) && i >= 0 && {
      val lenf = ssize(f)
      val lenr = ssize(r)
      (lenf >= 2 * lenr + 2 && lenf <= 2 * lenr + 3) && // size invariant between 'f' and 'r'
      lenf > i
    })
    val rval = r.value
    if(i < 2 || rval == SNil[T]()) { // A bug in Okasaki implementation: we must check for: 'rval = SNil()'
      val a: Lazy[Stream[T]] = SNil[T]()
      rotateRev(r, drop(i, f), a)
    } else {
      rval match {
        case SCons(x, rt) =>
          SCons(x, $(rotateDrop(rt, i - 2, drop(2, f))))
      }
    }
  } ensuring(res => res.size == (r*).size + (f*).size - i &&
      res.isCons && time <= 300)

  def firstUneval[T](l: Lazy[Stream[T]]): Lazy[Stream[T]] = {
    if (l.isEvaluated) {
      l* match {
        case SCons(_, tail) =>
          firstUneval(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => (!(res*).isEmpty || isConcrete(l)) &&
    ((res*).isEmpty || !res.isEvaluated) && // if the return value is not a Nil closure then it would not have been evaluated
    (res.value match {
      case SCons(_, tail) =>
        firstUneval(l) == firstUneval(tail) // after evaluating the firstUneval closure in 'l' we can access the next unevaluated closure
      case _ => true
    }))

  case class Queue[T](f: Lazy[Stream[T]], lenf: BigInt, sf: Lazy[Stream[T]],
      r: Lazy[Stream[T]], lenr: BigInt, sr: Lazy[Stream[T]]) {
    def isEmpty = lenf + lenr == 0
    def valid = {
      (firstUneval(f) == firstUneval(sf)) &&
        (firstUneval(r) == firstUneval(sr)) &&
        (lenf == ssize(f) && lenr == ssize(r)) &&
        (lenf <= 2*lenr + 1 && lenr <= 2*lenf + 1) &&
        {
          val mind = min(2*lenr-lenf+2, 2*lenf-lenr+2)
          ssize(sf) <= mind && ssize(sr) <= mind
        }
    }
  }

  /**
   * A function that takes streams where the size of front and rear streams violate
   * the balance invariant, and restores the balance.
   */
  def createQueue[T](f: Lazy[Stream[T]], lenf: BigInt, sf: Lazy[Stream[T]],
      r: Lazy[Stream[T]], lenr: BigInt, sr: Lazy[Stream[T]]): Queue[T] = {
    require(firstUneval(f) == firstUneval(sf) &&
        firstUneval(r) == firstUneval(sr) &&
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

  /**
   * Forces the schedules, and ensures that `firstUneval` equality is preserved
   */
  def force[T](tar: Lazy[Stream[T]], htar: Lazy[Stream[T]], other: Lazy[Stream[T]], hother: Lazy[Stream[T]]): Lazy[Stream[T]] = {
    require(firstUneval(tar) == firstUneval(htar) &&
      firstUneval(other) == firstUneval(hother))
    tar.value match {
      case SCons(_, tail) => tail
      case _              => tar
    }
  } ensuring (res => {
    //lemma instantiations
    val in = inState[Stream[T]]
    val out = outState[Stream[T]]
    funeMonotone(tar, htar, in, out) &&
      funeMonotone(other, hother, in, out) && {
      //properties
        val rsize = ssize(res)
          firstUneval(htar) == firstUneval(res) && // follows from post of fune
            firstUneval(other) == firstUneval(hother) &&
            (rsize == 0 || rsize == ssize(tar) - 1)
      } && time <= 350
  })

  /**
   * Forces the schedules in the queue twice and ensures the `firstUneval` property.
   */
  def forceTwice[T](q: Queue[T]): (Lazy[Stream[T]], Lazy[Stream[T]]) = {
    require(q.valid)
    val nsf = force(force(q.sf, q.f, q.r, q.sr), q.f, q.r, q.sr) // forces q.sf twice
    val nsr = force(force(q.sr, q.r, q.f, nsf), q.r, q.f, nsf) // forces q.sr twice
    (nsf, nsr)
  }
  // the following properties are ensured, but need not be stated
  /*ensuring (res => {
    val nsf = res._1
    val nsr = res._2
    firstUneval(q.f) == firstUneval(nsf) &&
      firstUneval(q.r) == firstUneval(nsr) &&
      (ssize(nsf) == 0 || ssize(nsf) == ssize(q.sf) - 2) &&
      (ssize(nsr) == 0 || ssize(nsr) == ssize(q.sr) - 2) &&
      time <= 1500
  })*/

  def empty[T] = {
    val nil: Lazy[Stream[T]] = SNil[T]()
    Queue(nil, 0, nil, nil, 0, nil)
  }

  /**
   * Adding an element to the front of the list
   */
  def cons[T](x: T, q: Queue[T]): Queue[T] = {
    require(q.valid)
    val nf: Stream[T] = SCons[T](x, q.f)
    // force the front and rear scheds once
    val nsf = force(q.sf, q.f, q.r, q.sr)
    val nsr = force(q.sr, q.r, q.f, nsf)
    createQueue(nf, q.lenf + 1, nsf, q.r, q.lenr, nsr)
  } ensuring (res => res.valid && time <= 1200)

  /**
   * Removing the element at the front, and returning the tail
   */
  def tail[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid)
    force(q.f, q.sf, q.r, q.sr) match { // force 'f'
      case _ =>
        tailSub(q)
    }
  } ensuring(res => res.valid && time <= 3000)

  def tailSub[T](q: Queue[T]): Queue[T] = {
    require(!q.isEmpty && q.valid && q.f.isEvaluated)
    q.f.value match {
      case SCons(x, nf) =>
        val (nsf, nsr) = forceTwice(q)
        // here, sf and sr got smaller by 2 holds, the schedule invariant still holds
        createQueue(nf, q.lenf - 1, nsf, q.r, q.lenr, nsr)
      case SNil() =>
         // in this case 'r' will have only one element by invariant
        empty[T]
    }
  } ensuring(res => res.valid && time <= 2750)

  /**
   * Reversing a list. Takes constant time.
   * This implies that data structure is a `deque`.
   */
  def reverse[T](q: Queue[T]): Queue[T] = {
    require(q.valid)
    Queue(q.r, q.lenr, q.sr, q.f, q.lenf, q.sf)
  } ensuring(q.valid && time <= 10)

   // Properties of `firstUneval`. We use `fune` as a shorthand for `firstUneval`
  /**
   * st1.subsetOf(st2) ==> fune(l, st2) == fune(fune(l, st1), st2)
   */
  @traceInduct
  def funeCompose[T](l1: Lazy[Stream[T]], st1: Set[Lazy[Stream[T]]], st2: Set[Lazy[Stream[T]]]): Boolean = {
    require(st1.subsetOf(st2))
    // property
    (firstUneval(l1) withState st2) == (firstUneval(firstUneval(l1) withState st1) withState st2)
  } holds

  /**
   * st1.subsetOf(st2) && fune(la,st1) == fune(lb,st1) ==> fune(la,st2) == fune(lb,st2)
   * The `fune` equality  is preseved by evaluation of lazy closures.
   * This is a kind of frame axiom for `fune` but is slightly different in that
   * it doesn't require (st2 \ st1) to be disjoint from la and lb.
   */
  def funeMonotone[T](l1: Lazy[Stream[T]], l2: Lazy[Stream[T]], st1: Set[Lazy[Stream[T]]], st2: Set[Lazy[Stream[T]]]): Boolean = {
    require((firstUneval(l1) withState st1) == (firstUneval(l2) withState st1) &&
        st1.subsetOf(st2))
     funeCompose(l1, st1, st2) && // lemma instantiations
     funeCompose(l2, st1, st2) &&
     // induction scheme
    (if (l1.isEvaluated withState st1) {
      l1* match {
        case SCons(_, tail) =>
          funeMonotone(tail, l2, st1, st2)
        case _ => true
      }
    } else true) &&
      (firstUneval(l1) withState st2) == (firstUneval(l2) withState st2) // property
  } holds
}
