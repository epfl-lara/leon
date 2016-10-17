package conqueue

import leon._
import collection._
import mem._
import higherorder._
import lang._
import math._
import annotation._
import instrumentation._
import invariant._

import conctrees.ConcTrees._

/**
 * This is file uses `ConcTrees` defined in file ConcTrees.scala.
 * This data structure is a queue of ConcTrees. 
 * The startegy used here is similar to `LazyNumericalRepresentation` but the contents
 * of the queue are not numbers but `ConcTrees` (see file ConTrees.scala).
 * Here, we prove that persistently enqueing an element into the tree will take constant time
 * in the worst case: function `pushLeftAndPay`.
 */
object Conqueue {

  sealed abstract class ConList[T] {
    @inline
    val isTip = this match {
      case _ : Tip[T] => true
      case _ => false
    }
    @inline
    val isSpine: Boolean = !isTip
  }

  case class Tip[T](t: Conc[T]) extends ConList[T]
  case class Spine[T](head: Conc[T], rear: Stream[T]) extends ConList[T]

  sealed abstract class Stream[T] {

    @inline
    def isSusp = this match {
      case _: Susp[T] => true
      case _       => false
    }

    lazy val fval = {
      require(isSusp)
      this match {
        case Susp(f) => f()
      }
    }

    def get: ConList[T] = {
      this match {
        case Susp(f) => fval
        case Val(x)  => x
      }
    }

    def getV = this match {
      case Susp(f) => fval*
      case Val(x)  => x
    }

    def isCached = this match {
      case _: Val[T] => true
      case _      => cached(fval)
    }
  }
  private case class Val[T](x: ConList[T]) extends Stream[T]
  private case class Susp[T](fun: () => ConList[T]) extends Stream[T]
  
  case class Conqueue[T](trees: Stream[T], schedule: List[Stream[T]]) {
    def valid = strongSchedsProp(trees, schedule)
  }

  def emptyNum[T] = {
    Conqueue[T](Val(Tip(Empty[T]())), Nil())
  } ensuring(_ => steps <= ?)

 /**
   * Checks whether there is a zero before an unevaluated closure
   */
  def zeroPrecedesLazy[T](q: Stream[T]): Boolean = {
    if (q.isCached) {
      q.getV match {
        case Spine(Empty(), rear) => true // here we have seen a zero
        case Spine(_, rear)      => zeroPrecedesLazy(rear) //here we have not seen a zero
        case Tip(_)               => true
      }
    } else false
  }

  /**
   * Checks whether there is a zero before a given suffix
   */
  @invisibleBody
  def zeroPrecedesSuf[T](q: Stream[T], suf: Stream[T]): Boolean = {
    if (q != suf) {
      q.getV match {
        case Spine(Empty(), rear) => true
        case Spine(_, rear)      => zeroPrecedesSuf(rear, suf)
        case Tip(_)               => false
      }
    } else false
  }

  /**
   * Everything until suf is evaluated. This
   * also asserts that suf should be a suffix of the list
   */
  @invisibleBody
  def concreteUntil[T](l: Stream[T], suf: Stream[T]): Boolean = {
    if (l != suf) {
      l.isCached && (l.getV match {
        case Spine(_, tail) => concreteUntil(tail, suf)
        case _              => false
      })
    } else true
  }

  @invisibleBody
  def isConcrete[T](l: Stream[T]): Boolean = {
    l.isCached && (l.getV match {
      case Spine(_, tail) => isConcrete(tail)
      case _              => true
    })
  }

  @invisibleBody
  def schedulesProperty[T](q: Stream[T], schs: List[Stream[T]]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        head match {
          case Susp(fun) =>
            concreteUntil(q, head) &&
              schedulesProperty(pushUntilCarry(head), tail)
          case _ => false
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  @invisibleBody
  def strongSchedsProp[T](q: Stream[T], schs: List[Stream[T]]) = {
    q.isCached &&
      (schs match {
        case Cons(head, tail) =>
          zeroPrecedesSuf(q, head) // zeroPrecedesSuf holds initially
        case Nil() => true
      }) &&
      schedulesProperty(q, schs)
  }

  /**
   * (a) If we push a carry and get back 0 then there is a new carry
   * (b) If we push a carry and get back 1 then there the carry has been fully pushed
   * Note that if 'q' has a suspension then it would have a carry.
   */
  @invisibleBody
  def pushUntilCarry[T](q: Stream[T]): Stream[T] = {
    q.getV match {
      case Spine(Empty(), rear) => // if we push a carry and get back 0 then there is a new carry
        pushUntilCarry(rear)
      case Spine(_, rear) => // if we push a carry and get back 1 then there the carry has been fully pushed
        rear
      case Tip(_) => q
    }
  }
  
  @invisibleBody
  def pushLeftStream[T](ys: Single[T], xs: Stream[T]): ConList[T] = {
    require(zeroPrecedesLazy(xs))
    xs.get match {
      case Tip(_ : CC[T]) =>
        Spine(ys, xs)
      case Tip(Empty()) => 
        Tip(ys)
      case Tip(t @ Single(_)) =>
        Tip(CC(ys, t))
      case s @ Spine(Empty(), rear) =>
        Spine(ys,rear)
      case s @ Spine(_, _) =>
        pushLeftLazy(ys, xs)
    }
  } ensuring (_ => steps <= ?)
  
  @invisibleBody
  @invstate
  def pushLeftLazy[T](ys: Conc[T], xs: Stream[T]): ConList[T] = {
    require(!ys.isEmpty && zeroPrecedesLazy(xs) &&
      xs.isCached &&
      (xs.getV match {
        case Spine(h, rear) => h != Empty[T]() && rear.isCached // xs is a spine and it doesn't start with a zero
        case _              => false
      }))
    xs.get match {
      case Spine(head, rear) => // here, rear is guaranteed to be evaluated by 'zeroPrecedeLazy' invariant
        val carry = CC(head, ys) //here, head and ys are of the same level
        rear.get match {
          case Tip(tree) =>
            if (tree.level > carry.level) { // here tree is of level at least two greater than rear ?              
              Spine(Empty[T](), Val(Spine(carry, rear)))
            } else { // here tree level and carry level are equal              
              Spine(Empty[T](), Val(Spine(Empty[T](), Val(Tip(CC(tree, carry))))))
            }
          case Spine(Empty(), srearfun) =>
            Spine(Empty[T](), Val(Spine(carry, srearfun)))

          case s =>
            Spine(Empty[T](), Susp(() => pushLeftLazy(carry, rear)))            
        }
    }
  } ensuring { res =>
    (res match {
      case Spine(Empty(), r) =>
        (r match {
          case _: Val[T]    => true
          case Susp(fun) => fun().isSpine // this is necessary to assert properties on the state in the recursive invocation
        }) &&
          (!isConcrete(xs) || isConcrete(pushUntilCarry(r)))
      case _ => false
    }) &&
      steps <= ?
  }  
  
  @invisibleBody
  def pushLeft[T](ys: Single[T], w: Conqueue[T]): (Stream[T], List[Stream[T]]) = {
    require(w.valid &&
      // instantiate the lemma that implies zeroPrecedesLazy
      (w.schedule match {
        case Cons(h, _) =>
          zeroPredSufConcreteUntilLemma(w.trees, h)
        case _ =>
          concreteZeroPredLemma(w.trees)
      }))
    val nq = pushLeftStream(ys, w.trees)
    val nsched = nq match {
      case Spine(Empty(), rear: Susp[T]) =>
        Cons(rear, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Val(nq), nsched)
  } ensuring { res =>
    // lemma instantiations
    (w.schedule match {
      case Cons(head, tail) =>
        w.trees.getV match {
          case Spine(h, _) =>
            if (h != Empty[T]())
              pushLeftLazyLemma(ys, w.trees, head)
            else true
          case _ => true
        }
      case _ => true
    }) &&
      schedulesProperty(res._1, res._2) &&
      steps <= ?
  }
  
  @invisibleBody
  def Pay[T](q: Stream[T], scheds: List[Stream[T]]): List[Stream[T]] = {
    require(schedulesProperty(q, scheds) && q.isCached)
    scheds match {
      case c @ Cons(head, rest) =>
        head.get match {
          case Spine(Empty(), rear: Susp[T]) => Cons(rear, rest)
          case _                         => rest
        }
      case Nil() => scheds
    }
  } ensuring { res =>
    payPostconditionInst(q, res, scheds, inSt[ConList[T]], outSt[ConList[T]]) && // properties
      schedulesProperty(q, res) &&
      steps <= ?
  }
  
   /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  @invisibleBody
  def pushLeftAndPay[T](ys: Single[T], w: Conqueue[T]) = {
    require(w.valid)
    val (q, scheds) = pushLeft(ys, w)
    val nscheds = Pay(q, scheds)
    Conqueue(q, nscheds)
  } ensuring { res => res.valid && steps <= ? }

  def head[T](w: Conqueue[T]): Conc[T] = {    
    w match {
      case  Conqueue(q, _) =>
        q.get match {
          case Tip(d) => d
          case Spine(d, _) => d
        }
    }        
  } 
  
  /**
   * Lemma instantiations (separated into a function for readability)
   */
  @inline
  def payPostconditionInst[T](q: Stream[T], res: List[Stream[T]], scheds: List[Stream[T]], in: Set[Fun[ConList[T]]], out: Set[Fun[ConList[T]]]) = {
    // instantiations for proving the scheds property
    (scheds match {
      case Cons(head, rest) =>
        concUntilExtenLemma(q, head, in, out) &&
          (head.getV match {
            case Spine(Empty(), rear) =>
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
          (concreteUntilIsSuffix(q, head) in in) &&
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
  }
  
  /**
   * Lemma:
   * \forall suf. suf.getV.head != Empty() ^ zeroPredsSuf(xs, suf) ^ concUntil(xs.tail.tail, suf) => concUntil(push(rear), suf)
   */
  @invisibleBody
  @invstate
  def pushLeftLazyLemma[T](ys: Conc[T], xs: Stream[T], suf: Stream[T]): Boolean = {
    require(!ys.isEmpty && zeroPrecedesSuf(xs, suf) &&
      (xs.getV match {
        case Spine(h, _) => h != Empty[T]()
        case _           => false
      }) && suf.isSusp && concreteUntil(xs, suf))
    // induction scheme
    (xs.getV match {
      case Spine(head, rear) =>
        val carry = CC[T](head, ys)
        rear.getV match {
          case s @ Spine(h, _) =>
            if (h != Empty[T]())
              pushLeftLazyLemma(carry, rear, suf)
            else true
          case _ => true
        }
    }) &&
      zeroPredSufConcreteUntilLemma(xs, suf) && // instantiate the lemma that implies zeroPrecedesLazy
      // property
      (pushLeftLazy(ys, xs) match {
        case Spine(Empty(), rear) =>
          concreteUntil(pushUntilCarry(rear), suf)
      })
  }.holds
  
  // monotonicity lemmas
  def schedMonotone[T](st1: Set[Fun[ConList[T]]], st2: Set[Fun[ConList[T]]], scheds: List[Stream[T]], l: Stream[T]): Boolean = {
    require(st1.subsetOf(st2) &&
      (schedulesProperty(l, scheds) in st1)) // here the input state is fixed as 'st1'
    //induction scheme
    (scheds match {
      case Cons(head, tail) =>
        head.getV match {
          case Spine(_, rear) =>
            concUntilMonotone(l, head, st1, st2) &&
              schedMonotone(st1, st2, tail, pushUntilCarry(head))
          case _ => true
        }
      case Nil() =>
        concreteMonotone(st1, st2, l)
    }) && (schedulesProperty(l, scheds) in st2) //property
  } holds

  @traceInduct
  def concreteMonotone[T](st1: Set[Fun[ConList[T]]], st2: Set[Fun[ConList[T]]], l: Stream[T]): Boolean = {
    ((isConcrete(l) in st1) && st1.subsetOf(st2)) ==> (isConcrete(l) in st2)
  } holds

  @traceInduct
  def concUntilMonotone[T](q: Stream[T], suf: Stream[T], st1: Set[Fun[ConList[T]]], st2: Set[Fun[ConList[T]]]): Boolean = {
    ((concreteUntil(q, suf) in st1) && st1.subsetOf(st2)) ==> (concreteUntil(q, suf) in st2)
  } holds

  // suffix predicates and  their properties (this should be generalizable)
  def suffix[T](q: Stream[T], suf: Stream[T]): Boolean = {
    if (q == suf) true
    else {
      q.getV match {
        case Spine(_, rear) =>
          suffix(rear, suf)
        case Tip(_) => false
      }
    }
  }

  def properSuffix[T](l: Stream[T], suf: Stream[T]): Boolean = {
    l.getV match {
      case Spine(_, rear) =>
        suffix(rear, suf)
      case _ => false
    }
  } ensuring (res => !res || (suffixDisequality(l, suf) && suf != l))

  /**
   * suf(q, suf) ==> suf(q.rear, suf.rear)
   */
  @traceInduct
  def suffixTrans[T](q: Stream[T], suf: Stream[T]): Boolean = {
    suffix(q, suf) ==> ((q.getV, suf.getV) match {
      case (Spine(_, rear), Spine(_, sufRear)) =>
        // 'sufRear' should be a suffix of 'rear1'
        suffix(rear, sufRear)
      case _ => true
    })
  }.holds

  /**
   * properSuf(l, suf) ==> l != suf
   */
  def suffixDisequality[T](l: Stream[T], suf: Stream[T]): Boolean = {
    require(properSuffix(l, suf))
    suffixTrans(l, suf) && // lemma instantiation
      ((l.getV, suf.getV) match { // induction scheme
        case (Spine(_, rear), Spine(_, sufRear)) =>
          // 'sufRear' should be a suffix of 'rear1'
          suffixDisequality(rear, sufRear)
        case _ => true
      }) && l != suf // property
  }.holds

  @traceInduct
  def suffixCompose[T](q: Stream[T], suf1: Stream[T], suf2: Stream[T]): Boolean = {
    (suffix(q, suf1) && properSuffix(suf1, suf2)) ==> properSuffix(q, suf2)
  } holds

  // properties of 'concUntil'

  @traceInduct
  def concreteUntilIsSuffix[T](l: Stream[T], suf: Stream[T]): Boolean = {
    concreteUntil(l, suf) ==> suffix(l, suf)
  }.holds

  // properties that extend `concUntil` to larger portions of the queue

  @traceInduct
  def concUntilExtenLemma[T](q: Stream[T], suf: Stream[T], st1: Set[Fun[ConList[T]]], st2: Set[Fun[ConList[T]]]): Boolean = {
    (suf.isSusp && (concreteUntil(q, suf) in st1) && (st2 == st1 ++ Set(Fun(suf.fval)))) ==>
      (suf.getV match {
        case Spine(_, rear) =>
          concreteUntil(q, rear) in st2
        case _ => true
      })
  } holds

  @traceInduct
  def concUntilConcreteExten[T](q: Stream[T], suf: Stream[T]): Boolean = {
    (concreteUntil(q, suf) && isConcrete(suf)) ==> isConcrete(q)
  } holds

  @traceInduct
  def concUntilCompose[T](q: Stream[T], suf1: Stream[T], suf2: Stream[T]): Boolean = {
    (concreteUntil(q, suf1) && concreteUntil(suf1, suf2)) ==> concreteUntil(q, suf2)
  } holds

  // properties that relate `concUntil`, `concrete`,  `zeroPrecedesSuf` with `zeroPrecedesLazy`
  //   - these are used in preconditions to derive the `zeroPrecedesLazy` property

  @traceInduct
  def zeroPredSufConcreteUntilLemma[T](q: Stream[T], suf: Stream[T]): Boolean = {
    (zeroPrecedesSuf(q, suf) && concreteUntil(q, suf)) ==> zeroPrecedesLazy(q)
  } holds

  @traceInduct
  def concreteZeroPredLemma[T](q: Stream[T]): Boolean = {
    isConcrete(q) ==> zeroPrecedesLazy(q)
  } holds

  // properties relating `suffix` an `zeroPrecedesSuf`

  def suffixZeroLemma[T](q: Stream[T], suf: Stream[T], suf2: Stream[T]): Boolean = {
    require(suf.getV match {
      case Spine(Empty(), _) =>
        suffix(q, suf) && properSuffix(suf, suf2)
      case _ => false
    })
    suffixCompose(q, suf, suf2) && (
      // induction scheme
      if (q != suf) {
        q.getV match {
          case Spine(_, tail) =>
            suffixZeroLemma(tail, suf, suf2)
          case _ =>
            true
        }
      } else true) &&
      zeroPrecedesSuf(q, suf2) // property
  }.holds
}

/* Used to simulate real conctrees in debugging
 * object ConcTrees {
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
}*/
