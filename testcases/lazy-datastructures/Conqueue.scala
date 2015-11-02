package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._

object Conqueue {

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  def zeroPreceedsLazy(q: $[ConQ[T]]): Boolean = {
    if (q.isEvaluated) {
      q* match {
        case Spine(Empty(), rear) =>
          true // here we have seen a zero
        case Spine(h, rear) =>
          zeroPreceedsLazy(rear) //here we have not seen a zero 
        case Tip(_) => true
      }
    } else false // this implies that a ConQ cannot start with a lazy closure
  }

  def isConcrete[T](l: $[ConQ[T]]): Boolean = {
    (l.isEvaluated && (l* match {
      case Spine(_, tail) =>
        isConcrete(tail)
      case _ => true
    })) || (l*).isEmpty
  }

  // an axiom about lazy streams (this should be a provable axiom, but not as of now)
  @axiom
  def streamLemma[T](l: $[ConQ[T]]) = {
    l.isEvaluated ||
      (l* match {
        case Spine(_, tail) =>
          l != tail && !tail.isEvaluated
        case _ => true
      })
  } holds

  def firstUnevaluated[T](l: $[ConQ[T]]): $[ConQ[T]] = {
    if (l.isEvaluated) {
      l* match {
        case Spine(_, tail) =>
          firstUnevaluated(tail)
        case _ => l
      }
    } else
      l
  } ensuring (res => ((res*).isSpine || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    ((res*).isTip || !res.isEvaluated) && // if the return value is not a Tip closure then it would not have been evaluated
    streamLemma(res) &&
    (res.value match {
      case SCons(_, tail) =>
        firstUnevaluated(l) == tail // after evaluating the firstUnevaluated closure in 'l' we get the next unevaluated closure
      case _ => true
    }))

  sealed abstract class ConQ[T] {
    val isSpine: Boolean = this match {
      case Spine(_, _) => true
      case _ => false
    }
    val isTip = !isSpine
  }

  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], rear: ConQ[T]) extends ConQ[T]

  def queueScheduleProperty[T](xs: $[ConQ[T]], sch: $[ConQ[T]]) = {
    xs.zeroPreceedsLazy && xs.firstLazyClosure == sch //sch is the first lazy closure of 's'          
  }

  sealed abstract class Scheds[T]
  case class Cons[T](h: $[ConQ[T]], tail: Scheds[T]) extends Scheds[T]
  case class Nil[T]() extends Scheds

  def schedulesProperty[T](q: $[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        queueScheduleProperty(q, head) && {
          val _ = head.value // evaluate the head and on the evaluated state the following should hold
          schedulesProperty(head, tail)
        }
      case Nil() =>
        q.isConcrete
    }
  }

  case class Wrapper[T](queue: ConQ[T], schedule: List[ConQ[T]]) {
    val valid: Boolean = {
      schedulesProperty(queue, schedule)
    }
  }

  def pushLeft[T](ys: Single[T], xs: $[ConQ[T]]): ConQ[T] = {
    require(xs.zeroPreceedsLazy)
    xs.value match {
      case Tip(CC(_, _)) =>
        Spine(ys, xs)
      case Tip(Empty()) =>
        Tip(ys)
      case Tip(t @ Single(_)) =>
        Tip(CC(ys, t))
      case Spine(_, _) =>
        pushLeftLazy(ys, xs) //ensure precondition here       
    }
  }  

  def pushLeftLazy[T](ys: Conc[T], xs: $[Spine[T]]): Spine[T] = {
    require(!ys.isEmpty && xs.zeroPreceedsLazy) // &&
    //(xs.head.isEmpty || xs.head.level == ys.level)) 

    xs.value match {
      case Spine(Empty(), rear) => //note: 'rear' is not materialized here         
        Spine(ys, rear) // if rear was 'PushLazy', this would temporarily break the 'zeroPreceedsLazy' invariant
      case Spine(head, rear) =>
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear match { //here, rear cannot be 'PushLazy' by the 'zeroPreceedsLazy' invariant
          case s @ Spine(Empty(), srear) =>
            Spine(Empty(), Spine(carry, srear))

          case s @ Spine(_, _) =>
            Spine(Empty(), PushLazy(carry, s))

          case t @ Tip(tree) if tree.level > carry.level => // can this happen ? this means tree is of level at least two greater than rear ?
            Spine(Empty(), Spine(carry, t))

          case Tip(tree) =>
            // here tree level and carry level are equal
            Spine(Empty(), Spine(Empty(), Tip(CC(tree, carry))))
        }
    }
  } ensuring (res => res.isSpine && res.weakValid)

  /**
   * Materialize will evaluate ps and update the references to
   * ps in xs. Ideally, the second argument should include every
   * structure that may contain 'pl'.
   */
  def materialize[T](mat: ConQ[T], xs: ConQ[T], schs: Cons[ConQ[T]]): (Spine[T], ConQ[T], BigInt) = {
    require(weakSchedulesProperty(xs, schs) && schs.head == mat)
    mat match {
      case PushLazy(elem, q) =>
        val (nr, t) = pushLeftLazy(elem, q)
        (nr, updateReferences(xs, mat, schs), t + 1)
    }
  } ensuring (res => (res._1 match {
    case Spine(_, pl @ PushLazy(_, _)) =>
      schedulesProperty(res._2, Cons(pl, schs.tail))
    case _ =>
      schedulesProperty(res._2, schs.tail)
  }) &&
    res._3 <= 2)

  /**
   * This does not take any time, by the definition of laziness
   */
  def updateReferences[T](xs: ConQ[T], mat: ConQ[T], schs: Cons[ConQ[T]]): ConQ[T] = {
    require(weakSchedulesProperty(xs, schs) && schs.head == mat)
    xs match {
      case Spine(h, pl @ PushLazy(elem, q)) if (pl == mat) =>
        //ADT property implies that we need not search in the sub-structure 'q'.
        Spine(h, pushLeftLazy(elem, q)._1) //here, we can ignore the time, this only captures the semantics      
      case Spine(h, rear) => //here mat and xs cannot be equal, so look in the substructures        
        Spine(h, updateReferences(rear, mat, schs))
    }
  } ensuring (res => mat match {
    case PushLazy(elem, q) =>
      pushLeftLazy(elem, q)._1 match {
        case Spine(_, pl @ PushLazy(_, _)) =>
          schedulesProperty(res, Cons(pl, schs.tail))
        case _ =>
          schedulesProperty(res, schs.tail)
      }
  })

  def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): (Wrapper[T], BigInt) = {
    require(w.valid)
    val (nq, t1) = pushLeft(ys, w.queue) // the queue invariant could be temporarily broken
    // update the schedule
    val nschs = nq match {
      case Spine(_, pl @ PushLazy(_, nest)) =>
        w.queue match {
          case Spine(head, rear) if !head.isEmpty =>
            Cons[ConQ[T]](pl, w.schedule)
          case _ =>
            w.schedule
        }
      case Tip(_) =>
        w.schedule
      case Spine(_, rear) =>
        w.schedule
    }
    val (fschs, fq, t2) = pay(nschs, nq)
    (Wrapper(fq, fschs), t1 + t2 + 1)
  } ensuring (res => res._1.valid && res._2 <= 6)

  def pay[T](schs: List[ConQ[T]], xs: ConQ[T]): (List[ConQ[T]], ConQ[T], BigInt) = {
    require(weakSchedulesProperty(xs, schs))
    schs match {
      case c @ Cons(pl @ PushLazy(_, nestq), rest) =>
        val (matr, nxs, matt) = materialize(pl, xs, c)
        matr match {
          case Spine(_, pl @ PushLazy(_, _)) =>
            (Cons(pl, rest), nxs, matt + 1)
          case _ =>
            (rest, nxs, matt + 1)
        }
      case Nil() =>
        (Nil(), xs, 1) // here every thing is concretized
    }
  } ensuring (res => schedulesProperty(res._2, res._1) &&
    res._3 <= 3)
}
