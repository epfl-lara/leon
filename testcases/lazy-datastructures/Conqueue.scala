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
  } //ensuring (res => !res || weakZeroPreceedsLazy(q)) //zeroPreceedsLazy is a stronger property

  /*def weakZeroPreceedsLazy[T](q: $[ConQ[T]]): Boolean = {
    q* match {
      case Spine(Empty(), rear) =>
        weakZeroPreceedsLazy(rear)
      case Spine(h, rear) =>
        zeroPreceedsLazy(rear) //here we have not seen a zero
      case Tip(_) => true
    }
  }*/

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
  } ensuring (res => ((res*).isSpine || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
    ((res*).isTip || !res.isEvaluated) && // if the return value is not a Tip closure then it would not have been evaluated
    streamLemma(res)  &&
    (res.value match {
      case Spine(_, tail) =>
        firstUnevaluated(l) == tail // after evaluating the firstUnevaluated closure in 'l' we get the next unevaluated closure
      case _ => true
    }))

  def nextUnevaluated[T](l: $[ConQ[T]]) : $[ConQ[T]] = {
    l* match {
      case Spine(_, tail) => firstUnevaluated(tail)
      case _ => l
    }
  }

  sealed abstract class ConQ[T] {
    val isSpine: Boolean = this match {
      case Spine(_, _) => true
      case _           => false
    }
    val isTip = !isSpine
  }

  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], rear: $[ConQ[T]]) extends ConQ[T]

  sealed abstract class Scheds[T]
  case class Cons[T](h: $[ConQ[T]], tail: Scheds[T]) extends Scheds[T]
  case class Nil[T]() extends Scheds[T]

  def schedulesProperty[T](q: $[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        (head*).isSpine &&
        (firstUnevaluated(q) == head) && { //sch is the first lazy closure of 's'
          val _ = head.value // evaluate the head and on the evaluated state the following should hold
          schedulesProperty(head, tail)
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  // this is a temporary property
  /*def weakSchedulesProperty[T](q: $[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        firstUnevaluated(q) == head && {
          val _ = head.value // evaluate the head and on the evaluated state the following should hold
          schedulesProperty(head, tail)
        }
      case Nil() =>
        isConcrete(q)
    }
  }*/

  case class Wrapper[T](queue: $[ConQ[T]], schedule: Scheds[T]) {
    val valid: Boolean = {
      zeroPreceedsLazy(queue) && schedulesProperty(queue, schedule)
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
      case s@Spine(_, _) =>
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
            val x : ConQ[T] = Spine(carry, srear)
            Spine(Empty(), $(x))

          case s @ Spine(_, _) =>
            Spine(Empty(), $(pushLeftLazy(carry, rear)))
          /*case s @ _ =>
            val e : ConQ[T] = Tip(Empty())
            Spine(Empty(), $(e))*/

          case t @ Tip(tree) =>
            if (tree.level > carry.level) { // can this happen ? this means tree is of level at least two greater than rear ?
              val x : ConQ[T] = t
              val y : ConQ[T] = Spine(carry, $(x))
              Spine(Empty(), $(y))
            }
            else {// here tree level and carry level are equal
              val x : ConQ[T] = Tip(CC(tree, carry))
              val y : ConQ[T] = Spine(Empty(), $(x))
              Spine(Empty(), $(y))
            }
        }
    }
  } ensuring (res => res.isSpine && (res match {
    case Spine(Empty(), rear) =>
      nextUnevaluated(rear) == firstUnevaluated(xs)
    case Spine(h, rear) =>
      firstUnevaluated(rear) == firstUnevaluated(xs)
    case _ => true
  }) || (firstUnevaluated(xs)*).isTip)

  def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): (ConQ[T], Scheds[T]) = {
    require(w.valid)
    val nq = pushLeft(ys, w.queue)
    val nsched = nq match {
        case Spine(Empty(), rear) =>
           Cons(rear, w.schedule)
        //case Spine(_, rear) =>
        //  firstUnevaluated(rear) == head
        case _ =>
          w.schedule
       }
    (nq, nsched)
  } ensuring (res => (res._2 match {
    case Cons(head, tail) =>
      res._1 match {
        case Spine(t, rear) =>
          (head*).isSpine &&
          firstUnevaluated(rear) == head && {
            val _ = head.value // evaluate the head and on the evaluated state the following should hold
              //if (!t.isEmpty)
                schedulesProperty(head, tail)
              //else true
          }
      }
    case _ =>
      res._1 match {
        case Spine(t, rear) =>
          isConcrete(rear)
        case _ => true
      }
  }))

  /*def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T]): Wrapper[T] = {
    require(w.valid)
    val pl = pushLeft(ys, w.queue)
    val nq = $(pl) // 'zeroPreceedsLazy' invariant could be temporarily broken
    // update the schedule
    // note that only when nq is a spine and the head of nq is empty new lazy closures will be created
    val tschs = nq.value match {
      case Spine(Empty(), rear) =>
        Cons(rear, w.schedule)
      case _ =>
        w.schedule
    }
    Wrapper(nq, pay(tschs, nq))
  }*/ //ensuring (res => res.valid) // && res._2 <= 6)

  /*def pay[T](schs: Scheds[T], xs: $[ConQ[T]]): Scheds[T] = {
    require(schs match {
      case Cons(h, t) =>
        xs.value match {
          case Spine(Empty(), rear) =>
            firstUnevaluated(xs) == h
        }
      case _ => true
    })//weakSchedulesProperty(xs, schs)) // we are not recursive here
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
  }*/ /*ensuring (res => schedulesProperty(res._2, res._1) &&
    res._3 <= 3)*/
}
