package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.collection._

object DigitObject {
  sealed abstract class Digit
  case class Zero() extends Digit {
    @ignore
    override def toString = "0"
  }
  case class One() extends Digit {
    @ignore
    override def toString = "1"
  }
}

import DigitObject._
object LazyNumericalRep {

  @finite
  sealed abstract class NumStream {
    @inline
    val isTip = this == Tip()

    @inline
    val isSpine: Boolean = !isTip

    @inline
    def rear = {
      this match {
        case Spine(_, Val(x))     => x
        case Spine(_, f @ Fun(_)) => f.get
      }
    }

    @inline
    def rearVal = {
      this match {
        case Spine(_, Val(x))     => x
        case Spine(_, f @ Fun(_)) => f.get*
      }
    }

    @inline
    def rearCached: Boolean = {
      this match {
        case Spine(_, f: Fun) => f.get.cached
        case _                   => true
      }
    }
  }

/*  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool
*/
  case class Tip() extends NumStream
  case class Spine(head: Digit, rearValorFun: ValOrFun) extends NumStream

  sealed abstract class ValOrFun {
    lazy val get: NumStream = {
      this match {
        case Fun(f) => f()
        case Val(x) => x
      }
    }
  }
  case class Val(x: NumStream) extends ValOrFun
  case class Fun(fun: () => NumStream) extends ValOrFun

  /**
   * Checks whether there is a zero before an unevaluated closure
   */
  def zeroPrecedeLazy(q: NumStream): Boolean = {
    //if (q.isEvaluated) {
    q match {
      case Spine(Zero(), _) => true // here we have seen a zero
      case s @ Spine(_, _) =>
        s.rearCached && zeroPrecedeLazy(s.rearVal) //here we have not seen a zero
      case Tip() => true
    }
//    /} else false
  }

  /**
   * Checks whether there is a zero before a given suffix
   */
  def zeroPrecedeSuf(q: NumStream, suf: NumStream): Boolean = {
    if (q != suf) {
      q match {
        case Spine(Zero(), _) => true
        case s@Spine(_, _) => zeroPrecedeSuf(s.rearVal, suf)
        case Tip() => false
      }
    } else false
  }

  /**
   * Everything until suf is evaluated. This
   * also asserts that suf should be a suffix of the list
   */
  def concreteUntil(l: NumStream, suf: NumStream): Boolean = {
    if (l != suf) {
     l match {
        case s@Spine(_, _) =>
          s.rearCached && concreteUntil(s.rearVal, suf)
        case _ =>
          false
      }
    } else true
  }

  def isConcrete(l: NumStream): Boolean = {
    l match {
      case s @ Spine(_, _) =>
        s.rearCached && isConcrete(s.rearVal)
      case _ => true
    }
  }

  /*sealed abstract class Scheds
  case class Cons(h: NumStream, tail: Scheds) extends Scheds
  case class Nil() extends Scheds*/

  def schedulesProperty(q: NumStream, schs: List[NumStream]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        head match {
          case Spine(Zero(), f: Fun) => // head starts with zero and has a suspension
            //head.isSuspension(incLazy _) &&
            concreteUntil(q, head) &&
              schedulesProperty(pushUntilCarry(f), tail)
          case _ => false
        }
      case Nil() => isConcrete(q)
    }
  }

  @invisibleBody
  def strongSchedsProp(q: NumStream, schs: List[NumStream]) = {
    (schs match {
      case Cons(head, tail) => zeroPrecedeSuf(q, head) // zeroPrecedeSuf holds initially
      case Nil()            => true
    }) &&
      schedulesProperty(q, schs)
  }

  /**
   * (a) If we push a carry and get back 0 then there is a new carry
   * (b) If we push a carry and get back 1 then there the carry has been fully pushed
   * Note that if 'q' has a suspension then it would have a carry.
   */
  @invisibleBody
  def pushUntilCarry(q: NumStream): NumStream = {
    q match {
      case Spine(_, rear: Fun) =>
        rear.get* match {
          case s@Spine(Zero(), _) => pushUntilCarry(s)
          case s => s
        }
      case s => s
    }
  }

  case class Number(digs: NumStream, schedule: List[NumStream]) {
    def isEmpty = digs.isTip
    def valid = strongSchedsProp(digs, schedule)
  }

  def emptyNum = Number(Tip(), Nil())

  @invisibleBody
  def inc(xs: NumStream): NumStream = {
    require(zeroPrecedeLazy(xs))
    xs match {
      case Tip() =>
        Spine(One(), Val(xs))
      case s @ Spine(Zero(), rearfun) =>
        Spine(One(), rearfun)
      case _  =>
        incLazy(xs)
    }
  } ensuring (_ => time <= ?)

  @invisibleBody
  @invstate
  def incLazy(xs: NumStream): NumStream = {
    require(zeroPrecedeLazy(xs) &&
      (xs match {
        case Spine(h, _) => h != Zero() // xs is a spine and it doesn't start with a zero
        case _              => false
      }))
    xs match {
      case s@Spine(head, rear) => // here, rear is guaranteed to be evaluated by 'zeroPrecedeLazy' invariant
        val carry = One()
        rear.get match {
          case Tip() =>
            Spine(Zero(), Val(Spine(carry, rear)))

          case s @ Spine(Zero(), srearfun) =>
            Spine(Zero(), Val(Spine(carry, srearfun)))

          case s =>
            Spine(Zero(), Fun(() => incLazy(s)))
        }
    }
  } ensuring { res =>
    (res match {
      case Spine(Zero(), f: Fun) =>
        (!isConcrete(xs) || isConcrete(pushUntilCarry(f))) &&
          {
            val _ = f.get // this is necessary to assert properties on the state in the recursive invocation (and note this cannot go first)
            f.get.cached // this is a tautology
          }
      case s: Spine => true
      case _ => false
    }) &&
      time <= ?
  }

  /**
   * Lemma:
   * forall suf. suf*.head != Zero() ^ zeroPredsSuf(xs, suf) ^ concUntil(xs.tail.tail, suf) => concUntil(push(rear), suf)
   */
  @invisibleBody
  @invstate
  def incLazyLemma(xs: NumStream, suf: NumStream): Boolean = {
    require(zeroPrecedeSuf(xs, suf) &&
      (xs match {
        case Spine(h, _) => h != Zero()
        case _              => false
      }) &&
      (suf match {
        case Spine(Zero(), _) => concreteUntil(xs, suf)
        case _ => false
      }))
    // induction scheme
    (xs.rear match {
      case s @ Spine(h, _) =>
        if (h != Zero())
          incLazyLemma(s, suf)
        else true
      case _ => true
    }) &&
      // instantiate the lemma that implies zeroPrecedeLazy
      (if (zeroPredSufConcreteUntilLemma(xs, suf)) {
        // property
        (incLazy(xs) match {
          case Spine(Zero(), rear: Fun) =>
            concreteUntil(pushUntilCarry(rear), suf)
          case _ => true
        })
      } else false)
  } holds

  @invisibleBody
  def incNum(w: Number) = {
    require(w.valid &&
      // instantiate the lemma that implies zeroPrecedeLazy
      (w.schedule match {
        case Cons(h, _) =>
          zeroPredSufConcreteUntilLemma(w.digs, h)
        case _ =>
          concreteZeroPredLemma(w.digs)
      }))
    val nq = inc(w.digs)
    val nsched = nq match {
      case s@Spine(Zero(), rfun: Fun) => Cons(s, w.schedule) // this is the only case where we create a new lazy closure
      case _ => w.schedule
    }
    (nq, nsched)
  } ensuring { res =>
    // lemma instantiations
    (w.schedule match {
      case Cons(head, tail) =>
        w.digs match {
          case Spine(h, _) =>
            if (h != Zero())
              incLazyLemma(w.digs, head)
            else true
          case _ => true
        }
      case _ => true
    }) &&
      schedulesProperty(res._1, res._2) &&
      time <= ?
  }

  @invisibleBody
  def Pay(q: NumStream, scheds: List[NumStream]): List[NumStream] = {
    require(schedulesProperty(q, scheds))
    scheds match {
      case c @ Cons(head, rest) =>
        head match {
          case Spine(Zero(), rear: Fun) => Cons(rear.get, rest) // evaluate rear one step
          case _ => rest
        }
      case Nil() => scheds
    }
  } ensuring { res =>
    {
      val in = inState[NumStream]
      val out = outState[NumStream]
      // instantiations for proving the scheds property
      (scheds match {
        case Cons(head, rest) =>
          concUntilExtenLemma(q, head, in, out) &&
            (head match {
              case s@Spine(Zero(), _) =>
                val rval = s.rearVal
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
        // instantiations for zeroPrecedeSuf property
        (scheds match {
          case Cons(head, rest) =>
            (concreteUntilIsSuffix(q, head) withState in) &&
              (res match {
                case Cons(rhead, rtail) =>
                  concreteUntilIsSuffix(pushUntilCarry(head), rhead) &&
                    suffixZeroLemma(q, head, rhead) &&
                    zeroPrecedeSuf(q, rhead)
                case _ =>
                  true
              })
          case _ =>
            true
        })
    } && // properties
      schedulesProperty(q, res) &&
      time <= ?
  }

  /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  @invisibleBody
  def incAndPay(w: Number) = {
    require(w.valid)

    val (q, scheds) = incNum(w)
    val nscheds = Pay(q, scheds)
    Number(q, nscheds)

  } ensuring { res => res.valid && time <= ? }

  def firstDigit(w: Number): Digit = {
    require(!w.isEmpty)
    w.digs.value match {
      case Spine(d, _, _) => d
    }
  }

  // monotonicity lemmas
  def schedMonotone(st1: Set[Lazy[NumStream]], st2: Set[Lazy[NumStream]], scheds: Scheds, l: Lazy[NumStream]): Boolean = {
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
  def concreteMonotone(st1: Set[Lazy[NumStream]], st2: Set[Lazy[NumStream]], l: Lazy[NumStream]): Boolean = {
    ((isConcrete(l) withState st1) && st1.subsetOf(st2)) ==> (isConcrete(l) withState st2)
  } holds

  @traceInduct
  def concUntilMonotone(q: Lazy[NumStream], suf: Lazy[NumStream], st1: Set[Lazy[NumStream]], st2: Set[Lazy[NumStream]]): Boolean = {
    ((concreteUntil(q, suf) withState st1) && st1.subsetOf(st2)) ==> (concreteUntil(q, suf) withState st2)
  } holds

  // suffix predicates and  their properties (this should be generalizable)

  def suffix(q: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
    if (q == suf) true
    else {
      q* match {
        case Spine(_, _, rear) =>
          suffix(rear, suf)
        case Tip() => false
      }
    }
  }

  def properSuffix(l: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
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
  def suffixTrans(q: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
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
  def suffixDisequality(l: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
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
  def suffixCompose(q: Lazy[NumStream], suf1: Lazy[NumStream], suf2: Lazy[NumStream]): Boolean = {
    (suffix(q, suf1) && properSuffix(suf1, suf2)) ==> properSuffix(q, suf2)
  } holds

  // properties of 'concUntil'

  @traceInduct
  def concreteUntilIsSuffix(l: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
    concreteUntil(l, suf) ==> suffix(l, suf)
  }.holds

  // properties that extend `concUntil` to larger portions of the queue

  @traceInduct
  def concUntilExtenLemma(q: Lazy[NumStream], suf: Lazy[NumStream], st1: Set[Lazy[NumStream]], st2: Set[Lazy[NumStream]]): Boolean = {
    ((concreteUntil(q, suf) withState st1) && st2 == st1 ++ Set(suf)) ==>
      (suf* match {
        case Spine(_, _, rear) =>
          concreteUntil(q, rear) withState st2
        case _ => true
      })
  } holds

  @traceInduct
  def concUntilConcreteExten(q: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
    (concreteUntil(q, suf) && isConcrete(suf)) ==> isConcrete(q)
  } holds

  @traceInduct
  def concUntilCompose(q: Lazy[NumStream], suf1: Lazy[NumStream], suf2: Lazy[NumStream]): Boolean = {
    (concreteUntil(q, suf1) && concreteUntil(suf1, suf2)) ==> concreteUntil(q, suf2)
  } holds

  // properties that relate `concUntil`, `concrete`,  `zeroPrecedeSuf` with `zeroPrecedeLazy`
  //   - these are used in preconditions to derive the `zeroPrecedeLazy` property

  @invisibleBody
  @traceInduct
  def zeroPredSufConcreteUntilLemma(q: Lazy[NumStream], suf: Lazy[NumStream]): Boolean = {
    (zeroPrecedeSuf(q, suf) && concreteUntil(q, suf)) ==> zeroPrecedeLazy(q)
  } holds

  @invisibleBody
  @traceInduct
  def concreteZeroPredLemma(q: Lazy[NumStream]): Boolean = {
    isConcrete(q) ==> zeroPrecedeLazy(q)
  } holds

  // properties relating `suffix` an `zeroPrecedeSuf`

  def suffixZeroLemma(q: Lazy[NumStream], suf: Lazy[NumStream], suf2: Lazy[NumStream]): Boolean = {
    require(suf* match {
      case Spine(Zero(), _, _) =>
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
      zeroPrecedeSuf(q, suf2) // property
  }.holds

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.BigNums
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._

    println("Running Numerical Representation test...")
    val ops = 1000000
    // initialize to a queue with one element (required to satisfy preconditions of dequeue and front)
    //var bignum: BigNums.BigNum = BigNums.Nil()
    var lazynum = emptyNum
    var totalTime1 = 0L
    var totalTime2 = 0L
    println(s"Testing amortized emphemeral behavior on $ops operations...")
    for (i <- 0 until ops) {
      //println("Inc..")
      //bignum = timed { BigNums.increment(bignum) } { totalTime1 += _ }
      lazynum = timed { incAndPay(lazynum) } { totalTime2 += _ }
      //val d1 = BigNums.firstDigit(bignum)
      val d2 = firstDigit(lazynum)
      //assert(d1.toString == d2.toString, s"Eager head: $d1 Lazy head: $d2")
    }
    println(s"Ephemeral Amortized Time - Eager: ${totalTime1 / 1000.0}s Lazy: ${totalTime2 / 1000.0}s") // this should be linear in length for both cases
    // now, test worst-case behavior (in persitent mode if necessary)
    val length = (1 << 22) - 1 // a number of the form: 2^{n-1}
    //bignum = BigNums.Nil()
    lazynum = emptyNum
    for (i <- 0 until length) {
      //bignum = BigNums.increment(bignum)
      lazynum = incAndPay(lazynum)
    }
    //println(s"Number of leading ones of bignum: ${BigNums.leadingOnes(bignum)}")
    //dequeue 1 element from both queues
    //timed { BigNums.increment(bignum) } { t => println(s"Time for one eager increment in the worst case: ${t / 1000.0}s") }
    timed { incAndPay(lazynum) } { t => println(s"Time for one lazy increment in the worst case: ${t / 1000.0}s") }
  }
}
