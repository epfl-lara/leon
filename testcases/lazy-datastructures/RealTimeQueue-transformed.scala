package leon
import lang._
import annotation._
import collection._

object RealTimeQueue {
  abstract class LList[T]

  def LList$isEmpty[T]($this: LList[T]): Boolean = {
    $this match {
      case SNil() =>
        true
      case _ =>
        false
    }
  }

  def LList$isCons[T]($this: LList[T]): Boolean = {
    $this match {
      case SCons(_, _) =>
        true
      case _ =>
        false
    }
  }

  def LList$size[T]($this: LList[T]): BigInt = {
    $this match {
      case SNil() =>
        BigInt(0)
      case SCons(x, t) =>
        BigInt(1) + ssize[T](t)
    }
  } ensuring {
    (x$1: BigInt) => (x$1 >= BigInt(0))
  }

  case class SCons[T](x: T, tail: LazyLList[T]) extends LList[T]

  case class SNil[T]() extends LList[T]

  // TODO: closures are not ADTs since two closures with same arguments are not necessarily equal but
  // ADTs are equal. This creates a bit of problem in checking if a closure belongs to a set or not.
  // However, currently we are assuming that such problems do not happen.
  // A solution is to pass around a dummy id that is unique for each closure.
  abstract class LazyLList[T]

  case class Rotate[T](f: LazyLList[T], r: List[T], a: LazyLList[T], res: LList[T]) extends LazyLList[T]

  case class Lazyarg[T](newa: LList[T]) extends LazyLList[T]

  def ssize[T](l: LazyLList[T]): BigInt = {
    val clist = evalLazyLList[T](l, Set[LazyLList[T]]())._1
    LList$size[T](clist)

  } ensuring (res => res >= 0)

  def isConcrete[T](l: LazyLList[T], st: Set[LazyLList[T]]): Boolean = {
    Set[LazyLList[T]](l).subsetOf(st) && (evalLazyLList[T](l, st)._1 match {
      case SCons(_, tail) =>
        isConcrete[T](tail, st)
      case _ =>
        true
    }) || LList$isEmpty[T](evalLazyLList[T](l, st)._1)
  }

  // an assertion: closures created by evaluating a closure will result in unevaluated closure
  @library
  def lemmaLazy[T](l: LazyLList[T], st: Set[LazyLList[T]]): Boolean = {
    Set[LazyLList[T]](l).subsetOf(st) || {
      evalLazyLList[T](l, Set[LazyLList[T]]())._1 match {
        case SCons(_, tail) =>
          l != tail && !Set[LazyLList[T]](tail).subsetOf(st)
        case _ => true
      }
    }
  } holds

  def firstUnevaluated[T](l: LazyLList[T], st: Set[LazyLList[T]]): LazyLList[T] = {
    if (Set[LazyLList[T]](l).subsetOf(st)) {
      evalLazyLList[T](l, st)._1 match {
        case SCons(_, tail) =>
          firstUnevaluated[T](tail, st)
        case _ =>
          l
      }
    } else {
      l
    }
  } ensuring (res => (!LList$isEmpty[T](evalLazyLList[T](res, st)._1) || isConcrete[T](l, st)) &&
    (LList$isEmpty[T](evalLazyLList[T](res, st)._1) || !Set[LazyLList[T]](res).subsetOf(st)) &&
    {
      val (nval, nst, _) = evalLazyLList[T](res, st)
      nval match {
        case SCons(_, tail) =>
          firstUnevaluated(l, nst) == tail
        case _ => true
      }
    } &&
    lemmaLazy(res, st))

  @library
  def evalLazyLList[T](cl: LazyLList[T], st: Set[LazyLList[T]]): (LList[T], Set[LazyLList[T]], BigInt) = {
    cl match {
      case t: Rotate[T] =>
        val (rres, _, rtime) = rotate(t.f, t.r, t.a, st)
        val tset = Set[LazyLList[T]](t)
        val tme =
          if (tset.subsetOf(st))
            BigInt(1)
          else // time of rotate
            rtime
        (rotate(t.f, t.r, t.a, Set[LazyLList[T]]())._1, st ++ tset, tme)

      case t: Lazyarg[T] =>
        (lazyarg(t.newa), st ++ Set[LazyLList[T]](t), BigInt(1))
    }
  } ensuring (res => (cl match {
    case t: Rotate[T] =>
      LList$size(res._1) == ssize(t.f) + t.r.size + ssize(t.a) &&
        res._1 != SNil[T]() &&
        res._3 <= 4
    case _ => true
  }) // &&
  //   (res._1 match {
  //       case SCons(_, tail) =>
  //         Set[LazyLList[T]](cl).subsetOf(st) || !Set[LazyLList[T]](tail).subsetOf(res._2)
  //       case _ => true
  //   })
  )

  @extern
  def rotate2[T](f: LazyLList[T], r: List[T], a: LazyLList[T], st: Set[LazyLList[T]]): (LList[T], Set[LazyLList[T]], BigInt) = ???

  def lazyarg[T](newa: LList[T]): LList[T] = {
    newa
  }

  def streamScheduleProperty[T](s: LazyLList[T], sch: LazyLList[T], st: Set[LazyLList[T]]): Boolean = {
    firstUnevaluated[T](s, st) == sch
  }

  case class Queue[T](f: LazyLList[T], r: List[T], s: LazyLList[T])

  def Queue$isEmpty[T]($this: Queue[T], st: Set[LazyLList[T]]): Boolean = {
    LList$isEmpty[T](evalLazyLList[T]($this.f, st)._1)
  }

  def Queue$valid[T]($this: Queue[T], st: Set[LazyLList[T]]): Boolean = {
    streamScheduleProperty[T]($this.f, $this.s, st) &&
      ssize[T]($this.s) == ssize[T]($this.f) - $this.r.size
  }

  // things to prove:
  // (a0) prove that pre implies post for 'rotate' (this depends on the assumption on eval)
  // (a) Rotate closure creations satisfy the preconditions of 'rotate' (or)
  //	for the preconditions involving state, the state at the Rotate invocation sites (through eval)
  // 	satisfy the preconditions of  'rotate'
  // (b) If we verify that preconditoins involving state hold at creation time,
  // 	 then we can assume them for calling time only if the preconditions are monotonic
  //	 with respect to inclusion of relation of state (this also have to be shown)
  // Note: using both captured and calling context is possible but is more involved
  // (c) Assume that 'eval' ensures the postcondition of 'rotate'
  // (d) Moreover we can also assume that the preconditons of rotate hold whenever we use a closure

  // proof of (a)
  // (i) for stateless invariants this can be proven by treating lazy eager,
  // so not doing this here

  // monotonicity of isConcrete
  def lemmaConcreteMonotone[T](f: LazyLList[T], st1: Set[LazyLList[T]], st2: Set[LazyLList[T]]): Boolean = {
    (evalLazyLList[T](f, st1)._1 match {
      case SCons(_, tail) =>
        lemmaConcreteMonotone(tail, st1, st2)
      case _ =>
        true
    }) &&
      !(st1.subsetOf(st2) && isConcrete(f, st1)) || isConcrete(f, st2)
  } holds

  // proof that the precondition isConcrete(f, st) holds for closure creation in 'rotate' function
  def rotateClosureLemma1[T](f: LazyLList[T], st: Set[LazyLList[T]]): Boolean = {
    require(isConcrete(f, st))
    val dres = evalLazyLList[T](f, st);
    dres._1 match {
      case SCons(x, tail) =>
        isConcrete(tail, st)
      case _ => true
    }
  } holds

  // proof that the precondition isConcrete(f, st) holds for closure creation in 'createQueue' function
  // @ important use and instantiate monotonicity of
  def rotateClosureLemma2[T](f: LazyLList[T], sch: LazyLList[T], st: Set[LazyLList[T]]): Boolean = {
    require(streamScheduleProperty[T](f, sch, st)) // && ssize[T](sch) == (ssize[T](f) - r.size) + BigInt(1))
    val dres4 = evalLazyLList[T](sch, st);
    dres4._1 match {
      case SNil() =>
        //isConcrete(f, dres4._2)
        isConcrete(f, st) // the above is implied by the monotonicity of 'isConcrete'
      case _ => true
    }
  } holds

  // proof that the precondition isConcrete(f, st) holds for closure creation in 'dequeue' function
  def rotateClosureLemma3[T](q: Queue[T], st: Set[LazyLList[T]]): Boolean = {
    require(!Queue$isEmpty[T](q, st) && Queue$valid[T](q, st))
    val dres7 = evalLazyLList[T](q.f, st);
    val SCons(x, nf) = dres7._1
    val dres8 = evalLazyLList[T](q.s, dres7._2);
    dres8._1 match {
      case SNil() =>
        isConcrete(nf, st)
      // the above would imply: isConcrete(nf, dres8._2) by monotonicity
      case _ => true
    }
  } holds

  // part(c) assume postconditon of 'rotate' in closure invocation time and also
  // the preconditions of 'rotate' if necesssary, and prove the properties of the
  // methods that invoke closures

  // proving specifications of 'rotate' (only state specifications are interesting)
  def rotate[T](f: LazyLList[T], r: List[T], a: LazyLList[T], st: Set[LazyLList[T]]): (LList[T], Set[LazyLList[T]], BigInt) = {
    require(r.size == ssize[T](f) + BigInt(1) && isConcrete(f, st))
    val dres = evalLazyLList[T](f, st);
    (dres._1, r) match {
      case (SNil(), Cons(y, _)) =>
        (SCons[T](y, a), dres._2, dres._3 + 2)
      case (SCons(x, tail), Cons(y, r1)) =>
        val na = Lazyarg[T](SCons[T](y, a))
        (SCons[T](x, Rotate[T](tail, r1, na, SNil[T]())), dres._2, dres._3 + 3)
    }
  } ensuring (res => LList$size(res._1) == ssize(f) + r.size + ssize(a) &&
    res._1 != SNil[T]() &&
    res._3 <= 4)

  // a stub for creating new closure (ensures that the new closures do not belong to the old state)
  // Note: this could result in inconsistency since we are associating unique ids with closures
  @library
  def newclosure[T](rt: Rotate[T], st: Set[LazyLList[T]]) = {
    (rt, st)
  } ensuring (res => !Set[LazyLList[T]](res._1).subsetOf(st))

  // proving specifications of 'createQueue' (only state specifications are interesting)
  def createQueue[T](f: LazyLList[T], r: List[T], sch: LazyLList[T], st: Set[LazyLList[T]]): (Queue[T], Set[LazyLList[T]], BigInt) = {
    require(streamScheduleProperty[T](f, sch, st) &&
      ssize[T](sch) == (ssize[T](f) - r.size) + BigInt(1))
    val dres4 = evalLazyLList[T](sch, st);
    dres4._1 match {
      case SCons(_, tail) =>
        (Queue[T](f, r, tail), dres4._2, dres4._3 + 2)
      case SNil() =>
        val rotres1 = newclosure(Rotate[T](f, r, Lazyarg[T](SNil[T]()), SNil[T]()), dres4._2); // can also directly call rotate here
        (Queue[T](rotres1._1, List[T](), rotres1._1), dres4._2, dres4._3 + 3)
    }
  } ensuring (res => Queue$valid[T](res._1, res._2) &&
    res._3 <= 7)

  // proving specifications of 'enqueue'
  def enqueue[T](x: T, q: Queue[T], st: Set[LazyLList[T]]): (Queue[T], Set[LazyLList[T]], BigInt) = {
    require(Queue$valid[T](q, st))
    createQueue[T](q.f, Cons[T](x, q.r), q.s, st)
  } ensuring (res => Queue$valid[T](res._1, res._2) &&
    res._3 <= 7)

  // proving specifications of 'dequeue'
  def dequeue[T](q: Queue[T], st: Set[LazyLList[T]]): (Queue[T], Set[LazyLList[T]], BigInt) = {
    require(!Queue$isEmpty[T](q, st) && Queue$valid[T](q, st))
    val dres7 = evalLazyLList[T](q.f, st);
    val SCons(x, nf) = dres7._1
    val dres8 = evalLazyLList[T](q.s, dres7._2);
    dres8._1 match {
      case SCons(_, nsch) =>
        (Queue[T](nf, q.r, nsch), dres8._2, dres7._3 + dres8._3 + 3)
      case _ =>
        val rotres3 = newclosure(Rotate[T](nf, q.r, Lazyarg[T](SNil[T]()), SNil[T]()), dres8._2);
        (Queue[T](rotres3._1, List[T](), rotres3._1), dres8._2, dres7._3 + dres8._3 + 4)
    }
  } ensuring (res => Queue$valid[T](res._1, res._2) &&
    res._3 <= 12)
}
