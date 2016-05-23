import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lang.synthesis._
import ConcTrees._
import ConQ._
import Conqueue._

object ConcTrees {
  abstract class Conc[T] {
    def isEmpty: Boolean = this == Empty[T]()

    def level: BigInt = {
      this match {
        case Empty() =>
          BigInt(0)
        case Single(x) =>
          BigInt(0)
        case CC(l, r) =>
          BigInt(1) + max(l.level, r.level)
      }
    } ensuring {
      (x$1: BigInt) => x$1 >= BigInt(0)
    }
  }

  case class Empty[T]() extends Conc[T]

  case class Single[T](x: T) extends Conc[T]

  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) {
    x
  } else {
    y
  }

  def abs(x: BigInt): BigInt = if (x < BigInt(0)) {
    -x
  } else {
    x
  }
}

object Conqueue {
  abstract class ConQ[T] {
    def isSpine: Boolean = this match {
      case Spine(_, _, _) =>
        true
      case _ =>
        false
    }
    def isTip: Boolean = !this.isSpine
  }

  case class Tip[T](t: Conc[T]) extends ConQ[T]

  case class Spine[T](head: Conc[T], createdWithSusp: Bool, rear: LazyConQ[T]) extends ConQ[T]

  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  abstract class Scheds[T]

  case class Cons[T](h: LazyConQ[T], tail: Scheds[T]) extends Scheds[T]

  case class Nil[T]() extends Scheds[T]

  case class Wrapper[T](queue: LazyConQ[T], schedule: Scheds[T]) {
    def valid(st: Set[LazyConQ[T]]): Boolean =
      strongSchedsProp(this.queue, this.schedule, st)
  }

  def zeroPreceedsLazy[T](q: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    if (isEvaluated(q, st)) {
      evalLazyConQS[T](q) match {
        case Spine(Empty(), _, rear) => true
        case Spine(_, _, rear) =>
          zeroPreceedsLazy[T](rear, st)
        case Tip(_) => true
      }
    } else false
  }

  // not used, but still interesting
  def zeroPredLazyMonotone[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q: LazyConQ[T]): Boolean = {
    require(st1.subsetOf(st2) && zeroPreceedsLazy(q, st1))
    zeroPreceedsLazy(q, st2) &&
      //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(Empty(), _, _) =>
          true
        case Spine(h, _, rear) =>
          zeroPredLazyMonotone(st1, st2, rear)
        case Tip(_) =>
          true
      })
  } holds

  def weakZeroPreceedsLazy[T](q: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    evalLazyConQS[T](q) match {
      case Spine(Empty(), _, rear10) =>
        true
      case Spine(h, _, rear11) =>
        zeroPreceedsLazy[T](rear11, st)
      case Tip(_) =>
        true
    }
  }

  def firstUnevaluated[T](l: LazyConQ[T], st: Set[LazyConQ[T]]): LazyConQ[T] = {
    if (isEvaluated(l, st)) {
      evalLazyConQS[T](l) match {
        case Spine(_, _, tail15) =>
          firstUnevaluated[T](tail15, st)
        case _ =>
          l
      }
    } else {
      l
    }
  } ensuring {
    (res65: LazyConQ[T]) =>
      (evalLazyConQS[T](res65).isTip || !st.contains(res65)) &&
        concreteUntil(l, res65, st)
  }

  def nextUnevaluatedLemma[T](l: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    val (res, nst) = evalLazyConQ[T](firstUnevaluated(l, st), st)
    (res match {
      case Spine(_, _, tail) =>
        firstUnevaluated[T](l, nst) == firstUnevaluated[T](tail, nst)
      case _ =>
        true
    }) &&
      // induction scheme
      (evalLazyConQS[T](l) match {
        case Spine(_, _, tail) =>
          nextUnevaluatedLemma(tail, st)
        case _ => true
      })
  } holds

  /**
   * Everything until suf is evaluated
   */
  def concreteUntil[T](l: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    if (l != suf) {
      isEvaluated(l, st) && (evalLazyConQS[T](l) match {
        case Spine(_, cws, tail15) =>
          concreteUntil(tail15, suf, st)
        case _ =>
          false // suf should in the queue
      })
    } else true
  }

  def concreteUntilIsSuffix[T](l: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(l, suf, st))
    suffix(l, suf) &&
     // induction scheme
    (if (l != suf) {
      (evalLazyConQS[T](l) match {
        case Spine(_, cws, tail15) =>
          concreteUntilIsSuffix(tail15, suf, st)
        case _ =>
          true
      })
    } else true)
  }.holds

  def isConcrete[T](l: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = isEvaluated(l, st) && (evalLazyConQS[T](l) match {
    case Spine(_, _, tail13) =>
      isConcrete[T](tail13, st)
    case _ =>
      true
  })

  def schedulesProperty[T](q: LazyConQ[T], schs: Scheds[T], st: Set[LazyConQ[T]]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        evalLazyConQS[T](head) match {
          case Spine(Empty(), _, _) =>
            !head.isInstanceOf[Eager[T]] &&
              concreteUntil(q, head, st) && schedulesProperty[T](pushUntilZero[T](head), tail, st)
          case _ =>
            false
        }
      case Nil() =>
        isConcrete(q, st)
    }
  }

  def strongSchedsProp[T](q: LazyConQ[T], schs: Scheds[T], st: Set[LazyConQ[T]]): Boolean = {
    isEvaluated(q, st) && {
      schs match {
        case Cons(head, tail) =>
          zeroPreceedsSuf(q, head) // zeroPreceedsSuf holds initially
        case Nil() => true
      }
    } &&
      schedulesProperty(q, schs, st)
  }

  // pushes a carry until there is a one
  // TODO: rename this to pushUntilCarry
  def pushUntilZero[T](q: LazyConQ[T]): LazyConQ[T] = evalLazyConQS[T](q) match {
    case Spine(Empty(), _, rear12) =>
      pushUntilZero[T](rear12)
    case Spine(h, _, rear13) =>
      rear13
    case Tip(_) =>
      q
  }

  // not used as of now
  def pushUntilZeroIsSuffix[T](q: LazyConQ[T]): Boolean = {
    suffix(q, pushUntilZero(q)) &&
    (evalLazyConQS[T](q) match {
      case Spine(Empty(), _, rear12) =>
        pushUntilZeroIsSuffix(rear12)
      case Spine(h, _, rear13) =>
        true
      case Tip(_) =>
        true
    })
  }.holds

  def pushLeft[T](ys: Single[T], xs: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    require(zeroPreceedsLazy[T](xs, st) && ys.isInstanceOf[Single[T]])

    val dres5 = evalLazyConQ[T](xs, st)
    dres5._1 match {
      case Tip(CC(_, _)) =>
        (Spine[T](ys, False(), xs), dres5._2)
      case Tip(Empty()) =>
        (Tip[T](ys), dres5._2)
      case Tip(t @ Single(_)) =>
        (Tip[T](CC[T](ys, t)), dres5._2)
      case s @ Spine(Empty(), _, rear) =>
        (Spine[T](ys, False(), rear), dres5._2) // in this case firstUnevaluated[T](rear, st) == firstUnevaluated[T](xs, st)
      case s @ Spine(_, _, _) =>
        pushLeftLazy[T](ys, xs, dres5._2)
    }
  }

/*  def dummyFun[T]() = ???[(ConQ[T], Set[LazyConQ[T]])]

  @library
  def pushLeftLazyUI[T](ys: Conc[T], xs: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    dummyFun()
  } ensuring (res => res._2 == st && (res._1 match {
    case Spine(Empty(), createdWithSusp, rear) =>
      true
    case _ => false
  }))*/

  def pushLeftLazyVal[T](ys: Conc[T], xs: LazyConQ[T]) : ConQ[T] = ???[ConQ[T]]

  @library
  def resSpec[T](ys: Conc[T], xs: LazyConQ[T], res : ConQ[T]) = {
    res == pushLeftLazyVal(ys, xs)
  } holds

  def pushLeftLazy[T](ys: Conc[T], xs: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    require(!ys.isEmpty && zeroPreceedsLazy[T](xs, st) &&
      (evalLazyConQS(xs) match {
        case Spine(h, _, _) => h != Empty[T]()
        case _              => false
      }))
    val dres = evalLazyConQ[T](xs, st)
    val res = dres._1 match {
      case Spine(head, _, rear15) =>
        val carry = CC[T](head, ys)
        val dres2 = evalLazyConQ[T](rear15, dres._2)
        dres2._1 match {
          case s @ Spine(Empty(), _, srear) =>
            (Spine[T](Empty[T](), False(), Eager(Spine(carry, False(), srear))), dres2._2)
          case s @ Spine(_, _, _) =>
            (Spine[T](Empty[T](), True(), PushLeftLazy[T](carry, rear15)), dres2._2)
          case t @ Tip(tree) =>
            if (tree.level > carry.level) { // this case may not even be possible given additional preconditions
              val x: ConQ[T] = t
              (Spine[T](Empty[T](), False(), Eager(Spine(carry, False(), rear15))), dres2._2)
            } else { // here tree level and carry level are equal
              val x: ConQ[T] = Tip[T](CC[T](tree, carry))
              (Spine[T](Empty[T](), False(), Eager(Spine(Empty[T](), False(), Eager[T](x)))), dres2._2)
            }
        }
    }
    res
  } ensuring {
    (res66: (Spine[T], Set[LazyConQ[T]])) =>
      resSpec(ys, xs, res66._1) &&  // asserts that the result is a function of inputs excluding state
      (res66._2 == st) && (res66._1 match {
        case Spine(Empty(), createdWithSusp, rear) =>
          val (rearval, _) = evalLazyConQ[T](rear, st) // this is necessary to assert properties on the state in the recursive invocation
          (!isConcrete(xs, st) || isConcrete(pushUntilZero(rear), st))
          //true
        case _ =>
          false
      })
  }

  def pushLeftLazyLemma[T](ys: Conc[T], xs: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(!ys.isEmpty && zeroPreceedsSuf(xs, suf) &&
      (evalLazyConQS(xs) match {
        case Spine(h, _, _) => h != Empty[T]() // this implies xs.rear is also evaluated
        case _              => false
      }) &&
      (evalLazyConQS(suf) match {
        case Spine(Empty(), _, _) =>
          concreteUntil(xs, suf, st)
        case _ => false
      }))
    // instantiate the lemma
    zeroPredSufConcreteUntilLemma(xs, suf, st) &&
    // property
    (pushLeftLazy(ys, xs, st)._1 match {
      case Spine(Empty(), createdWithSusp, rear) =>
        // forall suf. suf*.head == Empty() ^ concUntil(xs, suf, st) => concUntil(push(rear), suf, st)
        val p = pushUntilZero[T](rear)
        concreteUntil(p, suf, st)
    }) &&
      // induction scheme
      (evalLazyConQS(xs) match {
        case Spine(head, _, rear15) =>
          val carry = CC[T](head, ys)
          evalLazyConQS(rear15) match {
            case s @ Spine(h, _, _) if h != Empty[T]() =>
              pushLeftLazyLemma(carry, rear15, suf, st)
            case _ => true
          }
      })
  } holds

  def pushLeftWrapper[T](ys: Single[T], w: Wrapper[T], st: Set[LazyConQ[T]]) = {
    require(w.valid(st) && ys.isInstanceOf[Single[T]] &&
        // instantiate the lemma that implies zeroPreceedsLazy
        { w.schedule match {
          case Cons(h, _) =>
            zeroPredSufConcreteUntilLemma(w.queue, h, st)
          case _ =>
            concreteZeroPredLemma(w.queue, st)
        }})
    val (nq, nst) = pushLeft[T](ys, w.queue, st)
    val nsched = nq match {
      case Spine(Empty(), createdWithSusp, rear18) if createdWithSusp == True() =>
        Cons[T](rear18, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Eager(nq), nsched, nst)
  } ensuring { res =>
    // lemma instantiations
      (w.schedule match {
        case Cons(head, tail) =>
          evalLazyConQS(w.queue) match {
            case Spine(h, _, _) if h != Empty[T]() =>
              pushLeftLazyLemma(ys, w.queue, head, st)
            case _ => true
          }
        case _ => true
      }) && 
    //isEvaluated(res._1, res._3) &&
    schedulesProperty(res._1, res._2, res._3) // head of the schedule may start after the first element      
  }

  /*def PushLeftLazypushLeftLazyLem[T](rear15 : LazyConQ[T], head : Conc[T], dres : (ConQ[T], Set[LazyConQ[T]]), st : Set[LazyConQ[T]], xs : LazyConQ[T], s : Spine[T], dres : (ConQ[T], Set[LazyConQ[T]]), carry : CC[T], ys : Conc[T]): Boolean =  {
    (!ys.isEmpty && zeroPreceedsLazy[T](xs, st) && evalLazyConQS[T](xs).isSpine && dres == evalLazyConQ[T](xs, st) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && head == dres._1.head && rear15 == dres._1.rear && carry == CC[T](head, ys) && dres == evalLazyConQ[T](rear15, dres._2) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && s == dres._1) ==> (!carry.isEmpty && zeroPreceedsLazy[T](rear15, dres._2) && evalLazyConQS[T](rear15).isSpine)
  } ensuring {
    (holds : Boolean) => holds
  }*/

  def schedMonotone[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], scheds: Scheds[T], l: LazyConQ[T]): Boolean = {
    require(st1.subsetOf(st2) && schedulesProperty(l, scheds, st1))
    schedulesProperty(l, scheds, st2) && //property
      //induction scheme
      (scheds match {
        case Cons(head, tail) =>
          evalLazyConQS[T](head) match {
            case Spine(_, _, rear) =>
              concUntilMonotone(l, head, st1, st2) &&
                schedMonotone(st1, st2, tail, pushUntilZero(head))
            case _ => true
          }
        case Nil() =>
          concreteMonotone(st1, st2, l)
      })
  } holds

  def concreteMonotone[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], l: LazyConQ[T]): Boolean = {
    require(isConcrete(l, st1) && st1.subsetOf(st2))
    isConcrete(l, st2) && {
      // induction scheme
      evalLazyConQS[T](l) match {
        case Spine(_, _, tail) =>
          concreteMonotone[T](st1, st2, tail)
        case _ =>
          true
      }
    }
  } holds

  def concUntilExtenLemma[T](q: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf, st))
    val (next, nst) = evalLazyConQ[T](suf, st)
    (next match {
      case Spine(_, _, rear) =>
        concreteUntil(q, rear, nst)
      case _ => true
    }) &&
      (if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            concUntilExtenLemma(tail, suf, st)
          case _ =>
            true
        }
      } else true)
  } holds

  def concUntilExtenLemma2[T](q: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf, st) && isConcrete(suf, st))
    isConcrete(q, st) &&
      (if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            concUntilExtenLemma2(tail, suf, st)
          case _ =>
            true
        }
      } else true)
  } ensuring (_ == true)

  def concUntilCompose[T](q: LazyConQ[T], suf1: LazyConQ[T], suf2: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf1, st) && concreteUntil(suf1, suf2, st))
    concreteUntil(q, suf2, st) &&
      (if (q != suf1) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            concUntilCompose(tail, suf1, suf2, st)
          case _ =>
            true
        }
      } else true)
  } ensuring (_ == true)

  def concUntilMonotone[T](q: LazyConQ[T], suf: LazyConQ[T], st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf, st1) && st1.subsetOf(st2))
    concreteUntil(q, suf, st2) &&
      (if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            concUntilMonotone(tail, suf, st1, st2)
          case _ =>
            true
        }
      } else true)
  } ensuring (_ == true)

  /**
   * Not used in the proof
   */
  def concUntilZeroPredLemma[T](q: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf, st) && (evalLazyConQS(suf) match {
      case Spine(Empty(), _, _) => true
      case _                    => false
    }))
    val (next, nst) = evalLazyConQ[T](suf, st)
    zeroPreceedsLazy(q, nst) &&
      (if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            concUntilZeroPredLemma(tail, suf, st)
          case _ =>
            true
        }
      } else true)
  } holds

  def concreteZeroPredLemma[T](q: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(isConcrete(q, st))
    zeroPreceedsLazy(q, st) && {
      // induction scheme
      evalLazyConQS[T](q) match {
        case Spine(_, _, tail) =>
          concreteZeroPredLemma[T](tail, st)
        case _ =>
          true
      }
    }
  } holds

  def zeroPreceedsSuf[T](q: LazyConQ[T], suf: LazyConQ[T]): Boolean = {
    if (q != suf) {
      evalLazyConQS[T](q) match {
        case Spine(Empty(), _, rear) => true
        case Spine(_, _, rear) =>
          zeroPreceedsSuf(rear, suf)
        case Tip(_) => false
      }
    } else false
  }

  def zeroPredSufConcreteUntilLemma[T](q: LazyConQ[T], suf: LazyConQ[T], st: Set[LazyConQ[T]]): Boolean = {
    require(concreteUntil(q, suf, st) && zeroPreceedsSuf(q, suf))
    zeroPreceedsLazy(q, st) && {
      // induction scheme
      if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(Empty(), _, _) => true
          case Spine(_, _, tail) =>
            zeroPredSufConcreteUntilLemma(tail, suf, st)
          case _ =>
            true
        }
      } else true
    }
  } holds

  def Pay[T](q: LazyConQ[T], scheds: Scheds[T], st: Set[LazyConQ[T]]): (Scheds[T], Set[LazyConQ[T]]) = {
    require(schedulesProperty(q, scheds, st) && isEvaluated(q, st))
    val (nschs, rst) = scheds match {
      case c @ Cons(head, rest) =>
        val (headval, st2) = evalLazyConQ(head, st)
        (headval match {
          case Spine(Empty(), createdWithSusp, rear) => // note: no other case is possible
            if (createdWithSusp == True()) {
              Cons(rear, rest)
            } else
              rest
          //            In this case,
          //              val prear = pushUntilZero(rear)
          //            	concreteUntil(q, rhead, res._2) && concreteUntil(prear, rhead, st) && concreteUntil(rear, rhead, st) && schedulesProperty(prhead, rtail, st)
        }, st2)
      case Nil() =>
        (scheds, st)
    }
    (nschs, rst)
  } ensuring { res =>
    schedulesProperty(q, res._1, res._2) &&
    //strongSchedsProp(q, res._1, res._2) &&
      (scheds match {
        case Cons(head, rest) =>
          concUntilExtenLemma(q, head, st) &&
            (res._1 match {
              case Cons(rhead, rtail) =>
                val prhead = pushUntilZero(rhead)
                schedMonotone(st, res._2, rtail, prhead) &&
                  (evalLazyConQS(head) match {
                    case Spine(Empty(), cws, rear) =>
                      if (cws == False()) {
                        concUntilMonotone(rear, rhead, st, res._2) &&
                          concUntilCompose(q, rear, rhead, res._2)
                      } else true
                  })
              case _ =>
                evalLazyConQS(head) match {
                  case Spine(Empty(), _, rear) =>
                    concreteMonotone(st, res._2, rear) &&
                      concUntilExtenLemma2(q, rear, res._2)
                }
            })
        case _ => true
      }) &&
      // instantiations for zeroPreceedsSuf
      (scheds match {
        case Cons(head, rest) =>
          val phead = pushUntilZero(head)
          concreteUntilIsSuffix(q, head, st) &&
          (res._1 match {
            case Cons(rhead, rtail) =>
              concreteUntilIsSuffix(phead, rhead, st) &&
                suffixZeroLemma(q, head, rhead) &&
                zeroPreceedsSuf(q, rhead)
              //suffix(l, head) && head* == Spine(Empty(), _) && suffix(head, rhead) ==> zeroPreceedsSuf(l, rhead)
            case _ =>
              true
          })
        case _ =>
          true
      })
  }

  def suffix[T](q: LazyConQ[T], suf: LazyConQ[T]): Boolean = {
    if(q == suf) true
    else {
      evalLazyConQS(q) match {
        case Spine(_, _, rear) =>
          suffix(rear, suf)
        case Tip(_) => false
      }
    }
  }

  def suffixCompose[T](q: LazyConQ[T], suf1: LazyConQ[T],  suf2: LazyConQ[T]): Boolean = {
    require(suffix(q,suf1) && properSuffix(suf1, suf2))
    properSuffix(q, suf2) &&
    // induction over suffix(q, suf1)
    (if(q == suf1) true
    else {
      evalLazyConQS(q) match {
        case Spine(_, _, rear) =>
          suffixCompose(rear, suf1, suf2)
        case Tip(_) => false
      }
    })
  }.holds

  // TODO: this should be inferrable from the model
  @library
  def properSuffix[T](l: LazyConQ[T], suf: LazyConQ[T]) : Boolean = {
    evalLazyConQS(l) match {
      case Spine(_, _, rear) =>
        suffix(rear, suf)
      case _ => false
    }
  } ensuring(res => !res || suf != l)

  // uncomment this once the model is fixed
  /*def suffixInEquality[T](l: LazyConQ[T], suf: LazyConQ[T], suf2: ) : Boolean = {
    require(properSuffix(l, suf))
    (l != suf) && (
      evalLazyConQS(l) match {
        case Spine(_, _, rear) =>
          suffixInEquality(rear, suf)
        case _ => false
      })
  }.holds*/

  def suffixZeroLemma[T](q: LazyConQ[T], suf: LazyConQ[T], suf2: LazyConQ[T]): Boolean = {
    require(evalLazyConQS(suf) match {
      case Spine(Empty(), _, _) =>
        suffix(q, suf) && properSuffix(suf, suf2)
      case _ => false
    })
    suffixCompose(q, suf, suf2) &&
    zeroPreceedsSuf(q, suf2) && (
        // induction scheme
      if (q != suf) {
        evalLazyConQS[T](q) match {
          case Spine(_, _, tail) =>
            suffixZeroLemma(tail, suf, suf2)
          case _ =>
            true
        }
      } else true)
  }.holds

  def pushLeftAndPay[T](ys: Single[T], w: Wrapper[T], st: Set[LazyConQ[T]]) = {
    require(w.valid(st) && ys.isInstanceOf[Single[T]])
    val (q, scheds, nst) = pushLeftWrapper(ys, w, st)
    val (nscheds, fst) = Pay(q, scheds, nst)
    (Wrapper(q, nscheds), fst)
  } ensuring { res => res._1.valid(res._2) }

  def lazyarg1[T](x: ConQ[T]): ConQ[T] = x
}

object ConQ {

  abstract class LazyConQ[T1]

  case class Eager[T](x: ConQ[T]) extends LazyConQ[T]

  case class PushLeftLazy[T](ys: Conc[T], xs: LazyConQ[T] /*, suf: LazyConQ[T]*/ ) extends LazyConQ[T]

  @library
  def evalLazyConQ[T](cl: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    cl match {
      case t: Eager[T] =>
        (t.x, st)
      case t: PushLeftLazy[T] =>
        val (plres, plst) = pushLeftLazy[T](t.ys, t.xs, st)
        (plres, (plst ++ Set[LazyConQ[T]](t)))
    }
  } ensuring { res =>
    (cl match {
      case t : PushLeftLazy[T] =>
        res._1 == pushLeftLazyVal(t.ys, t.xs)
      case _ => true
    })
  }

  def simpLemma[T](cl : LazyConQ[T], st: Set[LazyConQ[T]]) :  Boolean = {
    evalLazyConQ(cl, st)._1 == evalLazyConQS(cl)
  }.holds

  def isEvaluated[T](cl: LazyConQ[T], st: Set[LazyConQ[T]]) = st.contains(cl) || cl.isInstanceOf[Eager[T]]

  def uiState[T](): Set[LazyConQ[T]] = ???[Set[LazyConQ[T]]]

  def evalLazyConQS[T](cl: LazyConQ[T]): ConQ[T] = evalLazyConQ[T](cl, uiState())._1

}
