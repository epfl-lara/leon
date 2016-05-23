package conc

import leon._
import lazyeval._
import lang._
import math._
import annotation._
import instrumentation._

import ConcTrees._

object ConcTrees {

  sealed abstract class Conc[T] {
    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    val level: BigInt = {
      this match {
        case Empty() => BigInt(0)
        case Single(x) => BigInt(0)
        case CC(l, r) =>
          BigInt(1) + max(l.level, r.level)
      }
    } ensuring (_ >= 0)
  }

  case class Empty[T]() extends Conc[T]
  case class Single[T](x: T) extends Conc[T]
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]
}

object Conqueue {

  sealed abstract class ConQ[T] {
    val isSpine: Boolean = this match {
      case Spine(_, _, _) => true
      case _ => false
    }
    val isTip = !isSpine
  }

  case class Tip[T](t: Conc[T]) extends ConQ[T]
  case class Spine[T](head: Conc[T], createdWithSuspension: Bool, rear: Lazy[ConQ[T]]) extends ConQ[T]

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  /**
   * Checks whether there is a zero before an unevaluated closure
   */
  def zeroPrecedesLazy[T](q: Lazy[ConQ[T]]): Boolean = {
    if (q.isEvaluated) {
      q* match {
        case Spine(Empty(), _, rear) =>
          true // here we have seen a zero
        case Spine(h, _, rear) =>
          zeroPrecedesLazy(rear) //here we have not seen a zero
        case Tip(_) => true
      }
    } else false
  }

  /**
   * Checks whether there is a zero before a given suffix
   */
  def zeroPrecedesSuf[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    if (q != suf) {
      q* match {
        case Spine(Empty(), _, rear) => true
        case Spine(_, _, rear) =>
          zeroPrecedesSuf(rear, suf)
        case Tip(_) => false
      }
    } else false
  }

  /**
   * Everything until suf is evaluated. This
   * also asserts that suf should be a suffix of the list
   */
  def concreteUntil[T](l: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    if (l != suf) {
      l.isEvaluated && (l* match {
        case Spine(_, cws, tail) =>
          concreteUntil(tail, suf)
        case _ =>
          false
      })
    } else true
  }

  def isConcrete[T](l: Lazy[ConQ[T]]): Boolean = {
    l.isEvaluated && (l* match {
      case Spine(_, _, tail) =>
        isConcrete(tail)
      case _ => true
    })
  }

  sealed abstract class Scheds[T]
  case class Cons[T](h: Lazy[ConQ[T]], tail: Scheds[T]) extends Scheds[T]
  case class Nil[T]() extends Scheds[T]

  def schedulesProperty[T](q: Lazy[ConQ[T]], schs: Scheds[T]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        head* match {
          case Spine(Empty(), _, _) =>
            head.isSuspension(pushLeftLazy[T] _) &&
              concreteUntil(q, head) &&
              schedulesProperty(pushUntilCarry(head), tail)
          case _ =>
            false
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  def strongSchedsProp[T](q: Lazy[ConQ[T]], schs: Scheds[T]) = {
    q.isEvaluated && {
      schs match {
        case Cons(head, tail) =>
          zeroPrecedesSuf(q, head) // zeroPrecedesSuf holds initially
        case Nil() => true
      }
    } &&
      schedulesProperty(q, schs)
  }

  /**
   * Note: if 'q' has a suspension then it would have a carry.
   */
  def pushUntilCarry[T](q: Lazy[ConQ[T]]): Lazy[ConQ[T]] = {
    q* match {
      case Spine(Empty(), _, rear) => // if we push a carry and get back 0 then there is a new carry
        pushUntilCarry(rear)
      case Spine(h, _, rear) => // if we push a carry and get back 1 then there the carry has been fully pushed
        rear
      case Tip(_) =>
        q
    }
  }

  case class Queue[T](queue: Lazy[ConQ[T]], schedule: Scheds[T]) {
    val valid = strongSchedsProp(queue, schedule)
  }

  def pushLeft[T](ys: Single[T], xs: Lazy[ConQ[T]]): ConQ[T] = {
    require(zeroPrecedesLazy(xs))
    xs.value match {
      case Tip(CC(_, _)) =>
        Spine(ys, False(), xs)
      case Tip(Empty()) =>
        Tip(ys)
      case Tip(t @ Single(_)) =>
        Tip(CC(ys, t))
      case s @ Spine(Empty(), _, rear) =>
        Spine[T](ys, False(), rear)
      case s @ Spine(_, _, _) =>
        pushLeftLazy(ys, xs)
    }
  } ensuring (_ => time <= 70)

  // this procedure does not change state
  @invstate
  def pushLeftLazy[T](ys: Conc[T], xs: Lazy[ConQ[T]]): ConQ[T] = {
    require(!ys.isEmpty && zeroPrecedesLazy(xs) &&
      (xs* match {
        case Spine(h, _, _) => h != Empty[T]()
        case _ => false
      }))
    xs.value match {
      case Spine(head, _, rear) => // here, rear is guaranteed to be evaluated by 'zeroPrecedesLazy' invariant
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear.value match {
          case s @ Spine(Empty(), _, srear) =>
            val tail: ConQ[T] = Spine(carry, False(), srear)
            Spine(Empty(), False(), tail)

          case s @ Spine(_, _, _) =>
            Spine(Empty(), True(), $(pushLeftLazy(carry, rear)))

          case t @ Tip(tree) =>
            if (tree.level > carry.level) { // can this happen ? this means tree is of level at least two greater than rear ?
              val y: ConQ[T] = Spine(carry, False(), rear)
              Spine(Empty(), False(), y)
            } else { // here tree level and carry level are equal
              val x: ConQ[T] = Tip(CC(tree, carry))
              val y: ConQ[T] = Spine(Empty(), False(), x)
              Spine(Empty(), False(), y)
            }
        }
    }
  } ensuring { res =>
    (res match {
      case Spine(Empty(), _, rear) =>
        (!isConcrete(xs) || isConcrete(pushUntilCarry(rear))) &&
          {
            val _ = rear.value // this is necessary to assert properties on the state in the recursive invocation (and note this cannot go first)
            rear.isEvaluated // this is a tautology
          }
      case _ =>
        false
    }) &&
      time <= 40
  }

  /**
   * Lemma:
   * forall suf. suf*.head != Empty() ^ zeroPredsSuf(xs, suf) ^ concUntil(xs.tail.tail, suf) => concUntil(push(rear), suf)
   */
  @invstate
  def pushLeftLazyLemma[T](ys: Conc[T], xs: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    require(!ys.isEmpty && zeroPrecedesSuf(xs, suf) &&
      (xs* match {
        case Spine(h, _, _) => h != Empty[T]()
        case _ => false
      }) &&
      (suf* match {
        case Spine(Empty(), _, _) =>
          concreteUntil(xs, suf)
        case _ => false
      }))
    // induction scheme
    (xs* match {
      case Spine(head, _, rear) =>
        val carry = CC[T](head, ys)
        rear* match {
          case s @ Spine(h, _, _) =>
            if (h != Empty[T]())
              pushLeftLazyLemma(carry, rear, suf)
            else true
          case _ => true
        }
    }) &&
      // instantiate the lemma that implies zeroPrecedesLazy
      (if (zeroPredSufConcreteUntilLemma(xs, suf)) {
        // property
        (pushLeftLazy(ys, xs) match {
          case Spine(Empty(), _, rear) =>
            concreteUntil(pushUntilCarry(rear), suf)
        })
      } else false)
  } holds

  def pushLeftWrapper[T](ys: Single[T], w: Queue[T]) = {
    require(w.valid &&
      // instantiate the lemma that implies zeroPrecedesLazy
      (w.schedule match {
        case Cons(h, _) =>
          zeroPredSufConcreteUntilLemma(w.queue, h)
        case _ =>
          concreteZeroPredLemma(w.queue)
      }))
    val nq = pushLeft(ys, w.queue)
    val nsched = nq match {
      case Spine(Empty(), createdWithSusp, rear) =>
        if (createdWithSusp == True())
          Cons[T](rear, w.schedule) // this is the only case where we create a new lazy closure
        else
          w.schedule
      case _ =>
        w.schedule
    }
    val lq: Lazy[ConQ[T]] = nq
    (lq, nsched)
  } ensuring { res =>
    // lemma instantiations
    (w.schedule match {
      case Cons(head, tail) =>
        w.queue* match {
          case Spine(h, _, _) =>
            if (h != Empty[T]())
              pushLeftLazyLemma(ys, w.queue, head)
            else true
          case _ => true
        }
      case _ => true
    }) &&
      schedulesProperty(res._1, res._2) &&
      time <= 80
  }

  def Pay[T](q: Lazy[ConQ[T]], scheds: Scheds[T]): Scheds[T] = {
    require(schedulesProperty(q, scheds) && q.isEvaluated)
    scheds match {
      case c @ Cons(head, rest) =>
        head.value match {
          case Spine(Empty(), createdWithSusp, rear) =>
            if (createdWithSusp == True())
              Cons(rear, rest)
            else
              rest
        }
      case Nil() => scheds
    }
  } ensuring { res =>
    {
      val in = inState[ConQ[T]]
      val out = outState[ConQ[T]]
      // instantiations for proving the scheds property
      (scheds match {
        case Cons(head, rest) =>
          concUntilExtenLemma(q, head, in, out) &&
            (head* match {
              case Spine(Empty(), _, rear) =>
                res match {
                  case Cons(rhead, rtail) =>
                    schedMonotone(in, out, rtail, pushUntilCarry(rhead)) &&
                      concUntilMonotone(rear, rhead, in, out) &&
                      concUntilCompose(q, rear, rhead)
                  case _ =>
                    concreteMonotone(in, out, rear) &&
                      concUntilConcreteExten(q, rear)
                }
            })
        case _ => true
      }) &&
        // instantiations for zeroPrecedesSuf property
        (scheds match {
          case Cons(head, rest) =>
            (concreteUntilIsSuffix(q, head) withState in) &&
              (res match {
                case Cons(rhead, rtail) =>
                  concreteUntilIsSuffix(pushUntilCarry(head), rhead) &&
                    suffixZeroLemma(q, head, rhead) &&
                    zeroPrecedesSuf(q, rhead)
                case _ =>
                  true
              })
          case _ =>
            true
        })
    } && // properties
      schedulesProperty(q, res) &&
      time <= 70
  }

  // monotonicity lemmas
  def schedMonotone[T](st1: Set[Lazy[ConQ[T]]], st2: Set[Lazy[ConQ[T]]], scheds: Scheds[T], l: Lazy[ConQ[T]]): Boolean = {
    require(st1.subsetOf(st2) &&
      (schedulesProperty(l, scheds) withState st1)) // here the input state is fixed as 'st1'
    //induction scheme
    (scheds match {
      case Cons(head, tail) =>
        head* match {
          case Spine(_, _, rear) =>
            concUntilMonotone(l, head, st1, st2) &&
              schedMonotone(st1, st2, tail, pushUntilCarry(head))
          case _ => true
        }
      case Nil() =>
        concreteMonotone(st1, st2, l)
    }) && (schedulesProperty(l, scheds) withState st2) //property
  } holds

  @traceInduct
  def concreteMonotone[T](st1: Set[Lazy[ConQ[T]]], st2: Set[Lazy[ConQ[T]]], l: Lazy[ConQ[T]]): Boolean = {
    ((isConcrete(l) withState st1) && st1.subsetOf(st2)) ==> (isConcrete(l) withState st2)
  } holds

  @traceInduct
  def concUntilMonotone[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]], st1: Set[Lazy[ConQ[T]]], st2: Set[Lazy[ConQ[T]]]): Boolean = {
    ((concreteUntil(q, suf) withState st1) && st1.subsetOf(st2)) ==> (concreteUntil(q, suf) withState st2)
  } holds

  // suffix predicates and  their properties (this should be generalizable)

  def suffix[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    if (q == suf) true
    else {
      q* match {
        case Spine(_, _, rear) =>
          suffix(rear, suf)
        case Tip(_) => false
      }
    }
  }

  def properSuffix[T](l: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    l* match {
      case Spine(_, _, rear) =>
        suffix(rear, suf)
      case _ => false
    }
  } ensuring (res => !res || (suffixDisequality(l, suf) && suf != l))

  /**
   * suf(q, suf) ==> suf(q.rear, suf.rear)
   */
  @traceInduct
  def suffixTrans[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    suffix(q, suf) ==> ((q*, suf*) match {
      case (Spine(_, _, rear), Spine(_, _, sufRear)) =>
        // 'sufRear' should be a suffix of 'rear1'
        suffix(rear, sufRear)
      case _ => true
    })
  }.holds

  /**
   * properSuf(l, suf) ==> l != suf
   */
  def suffixDisequality[T](l: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    require(properSuffix(l, suf))
    suffixTrans(l, suf) && // lemma instantiation
      ((l*, suf*) match { // induction scheme
        case (Spine(_, _, rear), Spine(_, _, sufRear)) =>
          // 'sufRear' should be a suffix of 'rear1'
          suffixDisequality(rear, sufRear)
        case _ => true
      }) && l != suf // property
  }.holds

  @traceInduct
  def suffixCompose[T](q: Lazy[ConQ[T]], suf1: Lazy[ConQ[T]], suf2: Lazy[ConQ[T]]): Boolean = {
    (suffix(q, suf1) && properSuffix(suf1, suf2)) ==> properSuffix(q, suf2)
  } holds

  // properties of 'concUntil'

  @traceInduct
  def concreteUntilIsSuffix[T](l: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    concreteUntil(l, suf) ==> suffix(l, suf)
  }.holds

  // properties that extend `concUntil` to larger portions of the queue

  @traceInduct
  def concUntilExtenLemma[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]], st1: Set[Lazy[ConQ[T]]], st2: Set[Lazy[ConQ[T]]]): Boolean = {
    ((concreteUntil(q, suf) withState st1) && st2 == st1 ++ Set(suf)) ==>
      (suf* match {
        case Spine(_, _, rear) =>
          concreteUntil(q, rear) withState st2
        case _ => true
      })
  } holds

  @traceInduct
  def concUntilConcreteExten[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    (concreteUntil(q, suf) && isConcrete(suf)) ==> isConcrete(q)
  } holds

  @traceInduct
  def concUntilCompose[T](q: Lazy[ConQ[T]], suf1: Lazy[ConQ[T]], suf2: Lazy[ConQ[T]]): Boolean = {
    (concreteUntil(q, suf1) && concreteUntil(suf1, suf2)) ==> concreteUntil(q, suf2)
  } holds

  // properties that relate `concUntil`, `concrete`,  `zeroPrecedesSuf` with `zeroPrecedesLazy`
  //   - these are used in preconditions to derive the `zeroPrecedesLazy` property

  @traceInduct
  def zeroPredSufConcreteUntilLemma[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]]): Boolean = {
    (zeroPrecedesSuf(q, suf) && concreteUntil(q, suf)) ==> zeroPrecedesLazy(q)
  } holds

  @traceInduct
  def concreteZeroPredLemma[T](q: Lazy[ConQ[T]]): Boolean = {
    isConcrete(q) ==> zeroPrecedesLazy(q)
  } holds

  // properties relating `suffix` an `zeroPrecedesSuf`

  def suffixZeroLemma[T](q: Lazy[ConQ[T]], suf: Lazy[ConQ[T]], suf2: Lazy[ConQ[T]]): Boolean = {
    require(suf* match {
      case Spine(Empty(), _, _) =>
        suffix(q, suf) && properSuffix(suf, suf2)
      case _ => false
    })
    suffixCompose(q, suf, suf2) && (
      // induction scheme
      if (q != suf) {
        q* match {
          case Spine(_, _, tail) =>
            suffixZeroLemma(tail, suf, suf2)
          case _ =>
            true
        }
      } else true) &&
      zeroPrecedesSuf(q, suf2) // property
  }.holds

  /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  def pushLeftAndPay[T](ys: Single[T], w: Queue[T]) = {
    require(w.valid)

    val (q, scheds) = pushLeftWrapper(ys, w)
    val nscheds = Pay(q, scheds)
    Queue(q, nscheds)

  } ensuring { res => res.valid && time <= 200 }
}
