package output
import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object MergeSort {

  case class Set1[T]()

  abstract class IList {
    def size: BigInt = {
      this match {
        case ICons(_, xs) =>
          BigInt(1) + xs.size
        case _ =>
          BigInt(0)
      }
    } ensuring {
      (x$1: BigInt) => x$1 >= BigInt(0)
    }
  }

  case class ICons(x: BigInt, tail: IList) extends IList

  case class INil() extends IList

  abstract class ILList {
    /*def size: BigInt = {
      this match {
        case LCons(_, xs37) =>
          BigInt(1) + ssize(xs37)
        case _ =>
          BigInt(0)
      }
    } ensuring {
      (x$218: BigInt) => x$218 >= BigInt(0)
    }*/
  }

  case class LCons(x: BigInt, tail: LazyILList) extends ILList

  case class LNil() extends ILList

  abstract class LList {
    def size: BigInt = {
      this match {
        case SNil() =>
          BigInt(0)
        case SCons(_, t) =>
          BigInt(1) + t.size
      }
    } ensuring {
      (x$3: BigInt) => x$3 >= BigInt(0)
    }
  }

  case class SCons(x: LazyILList, tail: LList) extends LList

  case class SNil() extends LList

 /* def ssize(l: LazyILList): BigInt = {
    evalLazyILList2(l).size
  } ensuring {
    (res: BigInt) => true
  }

  def fullSize(l: LList): BigInt = {
    l match {
      case SNil() =>
        BigInt(0)
      case SCons(l49, t) =>
        ssize(l49) + fullSize(t)
    }
  } ensuring {
    (x$46: BigInt) => x$46 >= BigInt(0)
  }*/

  /*def pairs(l: LList, st: Set1[LazyILList]): (LList, Set1[LazyILList]) = {
    l match {
      case SNil() =>
        (SNil(), st)
      case SCons(_, SNil()) =>
        (l, st)
      case SCons(l118, SCons(l215, rest)) =>
        val a77 = pairs(rest, st)
        (SCons(newILList(Merge(l118, l215), st), a77._1), a77._2)
    }
  } ensuring {
    (res69: (LList, Set1[LazyILList])) =>
      res69._1.size <= (l.size + BigInt(1)) / BigInt(2) &&
      fullSize(l) == fullSize(res69._1) &&
      time <= 10 * l.size + 4
  }*/

  abstract class LazyILList

  case class Merge(a: LazyILList, b: LazyILList) extends LazyILList

  case class Lsingle(x: BigInt) extends LazyILList

  case class Lempty() extends LazyILList

  //@library
  def newILList(cc: LazyILList, st: Set1[LazyILList]): LazyILList = {
    cc
  } /*ensuring {
    (res: LazyILList) => !st.contains(res)
  }*/

  //@library
  /*def evalLazyILList(cl: LazyILList, st: Set1[LazyILList]): (ILList, Set1[LazyILList]) = {
    cl match {
      case t: Merge =>
        (merge(t.a, t.b, Set1[LazyILList]()), Set1[LazyILList]())
      case t: Lsingle =>
        (lsingle(t.x, Set1[LazyILList]()), Set1[LazyILList]())
      case t: Lempty =>
        (lempty, Set1[LazyILList]())
    }
  } ensuring {
    (res: (ILList, Set1[LazyILList])) =>
      cl match {
        case t: Merge =>
          ssize(t.a) + ssize(t.b) == res._1.size &&
          time <= 300 * res._1.size  - 100
        case t: Lsingle =>
          true
        case t: Lempty =>
          true
      }
  }

  def evalLazyILList2(cl: LazyILList): ILList = {
    evalLazyILList(cl, Set1[LazyILList]())._1
  } ensuring {
    (res: ILList) => true
  }*/

/*  def constructMergeTree(l: LList, st: Set1[LazyILList]): (LList, Set1[LazyILList]) = {
    l match {
      case SNil() =>
        (SNil(), st)
      case SCons(_, SNil()) =>
        (l, st)
      case _ =>
        val a76 = pairs(l, st)
        constructMergeTree(a76._1, a76._2)
    }
  } ensuring {
    (res: (LList, Set1[LazyILList])) =>
      res._1.size <= BigInt(1) && fullSize(res._1) == fullSize(l) && (res._1 match {
        case SCons(il1, SNil()) =>
          fullSize(res._1) == ssize(il1)
        case _ =>
          true
      }) &&
      time <= 42 * l.size + 4
  }*/

  /*  def merge(a: LazyILList, b: LazyILList, st: Set1[LazyILList]): ILList = {
    require(evalLazyILList2(a) != LNil() && evalLazyILList2(b) != LNil())
    evalLazyILList(b, st)._1 match {
      case LNil() =>
        evalLazyILList(a, st)._1
      case bl @ LCons(x, xs36) =>
        evalLazyILList(a, st)._1 match {
          case LNil() =>
            bl
          case LCons(y, ys2) =>
            if (y < x) {
              LCons(y, Merge(ys2, b))
            } else {
              LCons(x, Merge(a, xs36))
            }
        }
    }
  } ensuring {
    (res70 : ILList) => ssize(a) + ssize(b) == res70.size &&
    time <= 300 * res70.size  - 100
//    (res70 match {
//      case _ if res70.size == 1 =>
//        time <= 300 * res70.size  + 100
//      case _ =>
//        time <= 300 * res70.size  - 100
//    })
  }*/

  def IListToLList(l: IList, st: Set1[LazyILList]): LList = {
    l match {
      case INil() =>
        SNil()
      case ICons(x, xs) =>
        SCons(newILList(Lsingle(x), st), IListToLList(xs, st))
    }
  } ensuring {
    (res: LList) =>
      //fullSize(res) == l.size && res.size == l.size &&
        time <= 9 * l.size + 3
  }

//  def mergeSort(l: IList, st: Set1[LazyILList]): (ILList, Set1[LazyILList]) = {
//    l match {
//      case INil() =>
//        (LNil(), st)
//      case _ =>
//        val scr = constructMergeTree(IListToLList(l, st), st)
//        scr._1 match {
//          case SCons(r13, SNil()) =>
//            val dres = evalLazyILList(r13, scr._2)
//            (dres._1, dres._2)
//        }
//    }
//  } ensuring {
//    (res: (ILList, Set1[LazyILList])) => true
//  }

  def lempty(): ILList = {
    LNil()
  } ensuring {
    (res: ILList) => true
  }

  def lsingle(x: BigInt, st: Set1[LazyILList]): ILList = {
    LCons(x, newILList(Lempty(), st))
  } ensuring {
    (res: ILList) => true
  }
}
