import leon.lazyeval._
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
    def valid(st: Set[LazyConQ[T]]): Boolean = zeroPreceedsLazy[T](this.queue, st) && schedulesProperty(this.queue, this.schedule, st)
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
      (evalLazyConQS[T](res65).isTip || !st.contains(res65)) /*&&
        {
          val dres4 = evalLazyConQ[T](res65, st)
          dres4._1 match {
            case Spine(_, _, tail16) =>
              firstUnevaluated[T](l, dres4._2) == firstUnevaluated[T](tail16, dres4._2)
            case _ =>
              true
          }
        }*/
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

  def schedulesProperty[T](q: LazyConQ[T], schs: Scheds[T], st: Set[LazyConQ[T]]): Boolean = {
    val x = firstUnevaluated(q, st)
    val y = evalLazyConQS(x)
    schs match {
      case Cons(head, tail) =>
        y.isSpine && x == head && schedulesProperty[T](pushUntilZero[T](head), tail, st) &&
          weakZeroPreceedsLazy(head, st)
      case Nil() =>
        y.isTip
    }
  }

  def pushUntilZero[T](q: LazyConQ[T]): LazyConQ[T] = evalLazyConQS[T](q) match {
    case Spine(Empty(), _, rear12) =>
      pushUntilZero[T](rear12)
    case Spine(h, _, rear13) =>
      rear13
    case Tip(_) =>
      q
  }

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
  } ensuring { res =>
    true
  }

  def dummyFun[T]() = ???[(ConQ[T], Set[LazyConQ[T]])]

  @library
  def pushLeftLazyUI[T](ys: Conc[T], xs: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    dummyFun()
  } ensuring (res => res._2 == st && (res._1 match {
    case Spine(Empty(), createdWithSusp, rear) =>
      val (rearval, _) = evalLazyConQ[T](rear, st) // this is necessary to assert properties on the state in the recursive invocation
      val p = pushUntilZero[T](rear)
      val fr = firstUnevaluated[T](p, st)
      rearval.isSpine && {
        if (createdWithSusp == False()) {
          fr == firstUnevaluated[T](rear, st)
        } else
          !isEvaluated(rear, st)
      } &&
        {
          val f = firstUnevaluated[T](xs, st)
          ((evalLazyConQS[T](f).isTip &&
            evalLazyConQS[T](fr).isTip) || fr == f)
        } &&
        weakZeroPreceedsLazy(rear, st)
    case _ => false
  }))

  def pushLeftLazy[T](ys: Conc[T], xs: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    require(!ys.isEmpty && zeroPreceedsLazy[T](xs, st) &&
      (evalLazyConQS[T](xs) match {
        case Spine(h, _, _) => h != Empty[T]()
        case _ => false
      }))
    val dres = evalLazyConQ[T](xs, st)
    dres._1 match {
      case Spine(head, _, rear15) =>
        val carry = CC[T](head, ys)
        val dres2 = evalLazyConQ[T](rear15, dres._2)
        dres2._1 match {
          case s @ Spine(Empty(), _, _) =>
            (Spine[T](Empty[T](), False(), Eager(Spine(carry, False(), rear15))), dres2._2)
          case s @ Spine(_, _, _) =>
            (Spine[T](Empty[T](), True(), newConQ[T](PushLeftLazy[T](carry, rear15), dres2._2)), dres2._2)
          case t @ Tip(tree) =>
            if (tree.level > carry.level) { // can this happen ? this means tree is of level at least two greater than rear ?
              val x: ConQ[T] = t
              (Spine[T](Empty[T](), False(), Eager(Spine(carry, False(), rear15))), dres2._2)
            } else { // here tree level and carry level are equal
              val x: ConQ[T] = Tip[T](CC[T](tree, carry))
              (Spine[T](Empty[T](), False(), Eager(Spine(Empty[T](), False(), Eager[T](x)))), dres2._2)
            }
        }
    }
  } ensuring {
    (res66: (Spine[T], Set[LazyConQ[T]])) =>
      (res66._2 == st) && (res66._1 match {
        case Spine(Empty(), createdWithSusp, rear) =>
          val (rearval, _) = evalLazyConQ[T](rear, st) // this is necessary to assert properties on the state in the recursive invocation
          val p = pushUntilZero[T](rear)
          val fr = firstUnevaluated[T](p, st)
          rearval.isSpine && {
            if (createdWithSusp == False()) {
              fr == firstUnevaluated[T](rear, st)
            } else
              !isEvaluated(rear, st)
          } &&
            {
              val f = firstUnevaluated[T](xs, st)
              ((evalLazyConQS[T](f).isTip &&
                evalLazyConQS[T](fr).isTip) || fr == f)
            } &&
            weakZeroPreceedsLazy(rear, st)
        case _ =>
          false
      })
  }

  def pushLeftWrapper[T](ys: Single[T], w: Wrapper[T], st: Set[LazyConQ[T]]) = {
    require(w.valid(st) && ys.isInstanceOf[Single[T]])
    val (nq, nst) = pushLeft[T](ys, w.queue, st)
    val nsched = nq match {
      case Spine(Empty(), createdWithSusp, rear18) if createdWithSusp == True() =>
        Cons[T](rear18, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Eager(nq), nsched, nst)
  } ensuring { res => schedulesProperty(res._1, res._2, res._3) }

  /*def PushLeftLazypushLeftLazyLem[T](rear15 : LazyConQ[T], head : Conc[T], dres : (ConQ[T], Set[LazyConQ[T]]), st : Set[LazyConQ[T]], xs : LazyConQ[T], s : Spine[T], dres : (ConQ[T], Set[LazyConQ[T]]), carry : CC[T], ys : Conc[T]): Boolean =  {
    (!ys.isEmpty && zeroPreceedsLazy[T](xs, st) && evalLazyConQS[T](xs).isSpine && dres == evalLazyConQ[T](xs, st) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && head == dres._1.head && rear15 == dres._1.rear && carry == CC[T](head, ys) && dres == evalLazyConQ[T](rear15, dres._2) && (!dres._1.isInstanceOf[Spine[T]] || !dres._1.head.isInstanceOf[Empty[T]]) && dres._1.isInstanceOf[Spine[T]] && s == dres._1) ==> (!carry.isEmpty && zeroPreceedsLazy[T](rear15, dres._2) && evalLazyConQS[T](rear15).isSpine)
  } ensuring {
    (holds : Boolean) => holds
  }*/

  def streamContains[T](l: LazyConQ[T], newl: LazyConQ[T]): Boolean = {
    (l == newl) || (evalLazyConQS[T](l) match {
      case Spine(_, _, tail) =>
        streamContains(tail, newl)
      case _ => false
    })
  }

  // monotonicity of fune
  def funeMonotone[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], l: LazyConQ[T], newl: LazyConQ[T]): Boolean = {
    require(st2 == st1 ++ Set(newl) &&
      !streamContains(l, newl))
    (firstUnevaluated(l, st1) == firstUnevaluated(l, st2)) && //property
      //induction scheme
      (evalLazyConQS[T](l) match {
        case Spine(_, _, tail) =>
          funeMonotone(st1, st2, tail, newl)
        case _ =>
          true
      })
  } holds

  @library // To be proven
  def schedMonotone[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], scheds: Scheds[T], l: LazyConQ[T], newl: LazyConQ[T]): Boolean = {
    require((st2 == st1 ++ Set(newl)) &&
      !streamContains(l, newl) && // newl is not contained in 'l'
      schedulesProperty(l, scheds, st1))

      funeMonotone(st1, st2, l, newl) && //instantiations
      schedulesProperty(l, scheds, st2) && //property
      //induction scheme
      (scheds match {
        case Cons(head, tail) =>
          (evalLazyConQS[T](head) match {
            case Spine(h, _, rear11) if h != Empty[T]()=>
              zeroPredLazyMonotone(st1, st2, rear11)
            case _ => true
          }) &&
          schedMonotone(st1, st2, tail, pushUntilZero(head), newl)
        case Nil() => true
      })
  } holds

  @library
  def dummyAxiom[T](l: LazyConQ[T], nl: LazyConQ[T]): Boolean = {
    !streamContains(l, nl)
  } holds

  def funeCompose[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q: LazyConQ[T]): Boolean = {
    require(st1.subsetOf(st2))
    (firstUnevaluated(firstUnevaluated(q, st1), st2) == firstUnevaluated(q, st2)) && //property
      //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(_, _, tail) =>
          funeCompose(st1, st2, tail)
        case _ =>
          true
      })
  } holds

  // induction following the structure of zeroPredLazy
  def funeZeroProp[T](st1: Set[LazyConQ[T]], st2: Set[LazyConQ[T]], q: LazyConQ[T]): Boolean = {
    require(st1.subsetOf(st2) && {
      val x = firstUnevaluated(q, st1)
      st2.contains(x) && weakZeroPreceedsLazy(x, st1)
    })
    zeroPreceedsLazy(q, st2) && //property
      //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(Empty(), _, tail) =>
          true
        case Spine(_, _, tail) =>
          (if (isEvaluated(q, st1))
            funeZeroProp(st1, st2, tail)
          else true)
        case _ =>
          true
      })
  } holds

  // induction following the structure of zeroPredLazy
  def funeZeroProp2[T](st: Set[LazyConQ[T]], q: LazyConQ[T]): Boolean = {
    require(evalLazyConQS(firstUnevaluated(q, st)).isTip)
    zeroPreceedsLazy(q, st) && //property
      //induction scheme
      (evalLazyConQS[T](q) match {
        case Spine(_, _, tail) =>
          funeZeroProp2(st, tail)
        case _ =>
          true
      })
  } holds

  def Pay[T](q: LazyConQ[T], scheds: Scheds[T], st: Set[LazyConQ[T]]): (Scheds[T], Set[LazyConQ[T]]) = {
    require(schedulesProperty(q, scheds, st) && isEvaluated(q, st))
    val (nschs, rst) = scheds match {
      case c @ Cons(head, rest) =>
        val (headval, st2) = evalLazyConQ(head, st)
        (headval match {
          case Spine(Empty(), createdWithSusp, rear) =>
            if (createdWithSusp == True()) {
              Cons(rear, rest)
            } else
              rest
//            In this case,
//              val p = pushUntilZero(rear)
//            	firstUnevaluated(q, res._2) == firstUnevaluated(rear, res._2) &&
//            	firstUnevaluated(p, st) == rhead &&
//            	rhead == firstUnevaluated(rear, st) &&
          case _ =>
            rest
          // Note: head has to be spine since scheds is not empty
          // in this case: firstUnevaluated[T](headval.rear, st) == rhead  && firstUnevaluated[T](q, res._2) == rhead by funeCompose
            //firstUnevaluated(rear, st) == rhead &&
          //schedulesProperty(pushUntilZero(head), res._1, st) &&
          //schedulesProperty(pushUntilZero(rhead), rtail, st)
          // schedMonotone(st, res._2, rtail, pushUntilZero(rhead), head)
        }, st2)
      case Nil() =>
        (scheds, st)
    }
    (nschs, rst)
  } ensuring { res =>
      zeroPreceedsLazy(q, res._2) &&
      schedulesProperty(q, res._1, res._2) &&
      // instantiations (relating rhead and head)
      funeCompose(st, res._2, q) &&
      (scheds match {
        case Cons(head, rest) =>
          (res._1 match {
            case Cons(rhead, rtail) =>
              val p = pushUntilZero(rhead)
              dummyAxiom(p, head) &&
                schedMonotone(st, res._2, rtail, p, head) &&
              {
                // an instantiation that could be packed into schedMonotone
                evalLazyConQS(rhead) match {
                  case Spine(h, _, rear11) if h != Empty[T]()=>
                  	zeroPredLazyMonotone(st, res._2, rear11)
                  case _ => true
                }
              }
            case _ => true
          }) &&
            (evalLazyConQS(head) match {
              case Spine(Empty(), cws, rear) =>
                dummyAxiom(rear, head) &&
                funeMonotone(st, res._2, rear, head) &&
                nextUnevaluatedLemma(q, st)
              case _ => true
            })
        case _ => true
      }) &&
      // instantiations for proving zeroPreceedsLazy property
      (scheds match {
        case Cons(head, rest) =>
          // establishing the zeroPreceedsLazy Property (on this case)
          //fune(q, st) == head && weakZero(head, st) && res._2 == st ++ { head }
          funeZeroProp(st, res._2, q) //instantiation
        case _ =>
          funeZeroProp2(st, q)
      })
  }

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

  case class PushLeftLazy[T](ys: Conc[T], xs: LazyConQ[T]) extends LazyConQ[T]

  @library
  def newConQ[T1](cc: LazyConQ[T1], st: Set[LazyConQ[T1]]): LazyConQ[T1] = {
    cc
  } ensuring {
    (res: LazyConQ[T1]) => !st.contains(res)
  }

  @library
  def evalLazyConQ[T](cl: LazyConQ[T], st: Set[LazyConQ[T]]): (ConQ[T], Set[LazyConQ[T]]) = {
    cl match {
      case t: Eager[T] =>
        (t.x, st)
      case t: PushLeftLazy[T] =>
        val plres = pushLeftLazyUI[T](t.ys, t.xs, uiState())._1
        val plst = pushLeftLazyUI[T](t.ys, t.xs, st)._2
        (plres, (plst ++ Set[LazyConQ[T]](t)))
    }
  }

  def isEvaluated[T](cl: LazyConQ[T], st: Set[LazyConQ[T]]) = st.contains(cl) || cl.isInstanceOf[Eager[T]]

  def uiState[T](): Set[LazyConQ[T]] = ???[Set[LazyConQ[T]]]

  def evalLazyConQS[T](cl: LazyConQ[T]): ConQ[T] = evalLazyConQ[T](cl, uiState())._1

}
