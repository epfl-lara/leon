package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._

object ConcTrees {

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  sealed abstract class Conc[T] {
    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    val level: BigInt = {
      (this match {
        case Empty()   => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)
  }

  case class Empty[T]() extends Conc[T]
  case class Single[T](x: T) extends Conc[T]
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]
}

import ConcTrees._
object Conqueue {

  def zeroPreceedsLazy[T](q: $[ConQ[T]]): Boolean = {
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
    })) || (l*).isTip
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
  } ensuring (res => //((res*).isSpine || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    //((res*).isTip || !res.isEvaluated) && // if the return value is not a Tip closure then it would not have been evaluated
    streamLemma(res)  &&
    /*(res.value match {
      case Spine(_, tail) =>
        firstUnevaluated(l) == tail // after evaluating the firstUnevaluated closure in 'l' we get the next unevaluated closure
      case _ => true
    })*/ true)

  sealed abstract class ConQ[T] {
    val isSpine: Boolean = this match {
      case Spine(_, _) => true
      case _           => false
    }
    val isTip = !isSpine
  }

  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], rear: $[ConQ[T]]) extends ConQ[T]

  def queueScheduleProperty[T](xs: $[ConQ[T]], sch: $[ConQ[T]]) = {
    zeroPreceedsLazy(xs) && firstUnevaluated(xs) == sch //sch is the first lazy closure of 's'
  }

  sealed abstract class Scheds[T]
  case class Cons[T](h: $[ConQ[T]], tail: Scheds[T]) extends Scheds[T]
  case class Nil[T]() extends Scheds[T]

  def schedulesProperty[T](q: $[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        queueScheduleProperty(q, head) && {
          val _ = head.value // evaluate the head and on the evaluated state the following should hold
          schedulesProperty(head, tail)
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  // this is a temporary property
  def weakSchedulesProperty[T](q: $[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        firstUnevaluated(q) == head && {
          val _ = head.value // evaluate the head and on the evaluated state the following should hold
          schedulesProperty(head, tail)
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  case class Wrapper[T](queue: $[ConQ[T]], schedule: Scheds[T]) {
    val valid: Boolean = {
      schedulesProperty(queue, schedule)
    }
  }

  def pushLeft[T](ys: Single[T], xs: $[ConQ[T]]): ConQ[T] = {
    require(zeroPreceedsLazy(xs))
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

  def pushLeftLazy[T](ys: Conc[T], xs: $[ConQ[T]]): ConQ[T] = {
    require(!ys.isEmpty && zeroPreceedsLazy(xs) && (xs*).isSpine)
    //(xs.head.isEmpty || xs.head.level == ys.level))
    xs.value match { //xs.value is evaluated by the 'zeroPreceedsLazy' invariant
      case Spine(Empty(), rear) =>
        Spine(ys, rear) // if rear is an unevaluated 'pushLazy', this would temporarily break the 'zeroPreceedsLazy' invariant
      case Spine(head, rear) =>
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear.value match {
          //if rear.value is spine it has to be evaluated by the 'zeroPreceedsLazy' invariant
          // otherwise, rear.value should be tip
          case s @ Spine(Empty(), srear) =>
            Spine(Empty(), $[ConQ[T]](Spine(carry, srear)))

          case s @ Spine(_, _) =>
            Spine(Empty(), $(pushLeftLazy(carry, rear)))

          case t @ Tip(tree) =>
            if (tree.level > carry.level) // can this happen ? this means tree is of level at least two greater than rear ?
              Spine(Empty(), $[ConQ[T]](Spine(carry, $[ConQ[T]](t))))
            else // here tree level and carry level are equal
              Spine(Empty(), $[ConQ[T]](Spine(Empty(), $[ConQ[T]](Tip(CC(tree, carry))))))
        }
    }
  } ensuring (res => res match { // However, the weakZeroPreceedsLazy property would hold
    case Spine(Empty(), _) => true
    case Spine(h, rear) =>
      val _ = rear.value
      zeroPreceedsLazy(rear) // zeroPreceedsLazy should hold in the evaluated state
    case _ => false
  })

  /**
   * Materialize will evaluate ps and update the references to
   * ps in xs. Ideally, the second argument should include every
   * structure that may contain 'pl'.
   */
  /*  def materialize[T](mat: ConQ[T], xs: ConQ[T], schs: Cons[ConQ[T]]): (Spine[T], ConQ[T], BigInt) = {
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

  */
  /**
   * This does not take any time, by the definition of laziness
   */ /*
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
  })*/

  def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): Wrapper[T] = {
    require(w.valid)
    val nq = $(pushLeft(ys, w.queue)) // 'zeroPreceedsLazy' invariant could be temporarily broken
    // update the schedule
    // note that only when nq is a spine and the head of nq is empty a lazy closures will be created
    val tschs = nq.value match {
      case Spine(Empty(), rear) =>
        Cons(rear, w.schedule)
      case _ =>
        w.schedule
    }
    Wrapper(nq, pay(tschs, nq))
  } ensuring (res => res.valid) // && res._2 <= 6)

  def pay[T](schs: Scheds[T], xs: $[ConQ[T]]): Scheds[T] = {
    require(weakSchedulesProperty(xs, schs)) // we are not recursive here
    schs match {
      case c @ Cons(head, rest) =>
        head.value match {
          case Spine(Empty(), rear) =>
            Cons(rear, rest) // here, new lazy closures are created
          case _ =>
            rest
        }
      case Nil() =>
        // here every thing is concretized
        schs
    }
  } /*ensuring (res => schedulesProperty(res._2, res._1) &&
    res._3 <= 3)*/
}
