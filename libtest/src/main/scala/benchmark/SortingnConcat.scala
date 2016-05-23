import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.runtimeDriver._

////////////////////////////////////////////////

object SortingnConcat0 {
  abstract class LList0
  
  case class SCons0(x0 : BigInt, tailFun0 : Stream0) extends LList0
  
  case class SNil0() extends LList0
  
  case class Stream0(lfun1 : tLList0) {
    def listmemtime0(st5 : Set[MemoFuns0]): ((LList0, Set[MemoFuns0]), BigInt) = {
      val e57 = evaltLListtime0(this.lfun1)
      ((e57._1, st5), BigInt(3) + e57._2)
    }
  }
  
  def pullMintime0(l39 : List[BigInt]): (List[BigInt], BigInt) = {
    val bd5 = l39 match {
      case Nil() =>
        (l39, BigInt(2))
      case Cons(x15, xs2) =>
        val e66 = pullMintime0(xs2)
        val scr8 = BigInt(1) + e66._2
        val mc11 = e66._1 match {
          case Nil() =>
            (Cons[BigInt](x15, Nil[BigInt]()), BigInt(4) + scr8)
          case nxs0 @ Cons(y6, ys0) =>
            val mc10 = if (x15 <= y6) {
              (Cons[BigInt](x15, nxs0), BigInt(3))
            } else {
              (Cons[BigInt](y6, Cons[BigInt](x15, ys0)), BigInt(4))
            }
            (mc10._1, (BigInt(5) + mc10._2) + scr8)
        }
        (mc11._1, BigInt(5) + mc11._2)
    }
    (bd5._1, bd5._2)
  }
  
  def sorttime0(l40 : List[BigInt]): (LList0, BigInt) = {
    val e42 = pullMintime0(l40)
    val scr12 = BigInt(1) + e42._2
    val bd1 = e42._1 match {
      case Cons(x16, xs3) =>
        (SCons0(x16, Stream0(SortL0(xs3))), BigInt(7) + scr12)
      case _ =>
        (SNil0(), BigInt(3) + scr12)
    }
    (bd1._1, bd1._2)
  }
  
  def concattime0(l118 : List[BigInt], l216 : LList0): (LList0, BigInt) = {
    val bd4 = l118 match {
      case Cons(x17, xs4) =>
        (SCons0(x17, Stream0(ConcatL0(xs4, l216))), BigInt(7))
      case Nil() =>
        (SNil0(), BigInt(4))
    }
    (bd4._1, bd4._2)
  }
  
  def kthMintime0(l41 : Stream0, k4 : BigInt, st3 : Set[MemoFuns0]): ((BigInt, Set[MemoFuns0]), BigInt) = {
    val e16 = l41.listmemtime0(st3)
    val e92 = e16._1
    val e102 = e92._2 ++ Set[MemoFuns0](ListmemM0(l41))
    val r160 = e92._1 match {
      case SCons0(x18, xs5) =>
        val mc0 = if (k4 == BigInt(1)) {
          ((x18, e102), BigInt(4))
        } else {
          val e35 = kthMintime0(xs5, k4 - BigInt(1), e102)
          (e35._1, BigInt(5) + e35._2)
        }
        (mc0._1, BigInt(5) + mc0._2)
      case SNil0() =>
        ((BigInt(0), e102), BigInt(6))
    }
    (r160._1, (BigInt(8) + r160._2) + (if (st3.contains(ListmemM0(l41))) {
      BigInt(1)
    } else {
      BigInt(1) + e16._2
    }))
  }
    
  abstract class tLList0
  
  case class SortL0(xs36 : List[BigInt]) extends tLList0
  
  case class ConcatL0(xs37 : List[BigInt], l215 : LList0) extends tLList0
  
  abstract class MemoFuns0
  
  case class ListmemM0(thiss634 : Stream0) extends MemoFuns0
  
  @axiom
  def evaltLListtime0(cl1 : tLList0): (LList0, BigInt) = {
    val bd2 = cl1 match {
      case t378 : SortL0 =>
        val e49 = sorttime0(t378.xs36)
        (e49._1, BigInt(4) + e49._2)
      case t379 : ConcatL0 =>
        val e54 = concattime0(t379.xs37, t379.l215)
        (e54._1, BigInt(5) + e54._2)
    }
    (bd2._1, bd2._2)
  }
  
}

object LList1 {
}

object Stream1 {
}
///////////////////////////////////////////////////////////


object SortingnConcat {  
  abstract class LList2

  case class SCons1(x316 : BigInt, tailFun1 : Stream2) extends LList2
  
  case class SNil1() extends LList2
  
  case class Stream2(lfun1 : () => (LList2, BigInt))
  
  def pullMintime(l : List[BigInt]): (List[BigInt], BigInt) = {
    val bd4 = l match {
      case Nil() =>
        (l, BigInt(2))
      case Cons(x, xs) =>
        val e34 = pullMintime(xs)
        val scr8 = BigInt(1) + e34._2
        val mc7 = e34._1 match {
          case Nil() =>
            (List[BigInt](x), BigInt(4) + scr8)
          case nxs @ Cons(y, ys) =>
            val mc6 = if (x <= y) {
              (Cons[BigInt](x, nxs), BigInt(3))
            } else {
              (Cons[BigInt](y, Cons[BigInt](x, ys)), BigInt(4))
            }
            (mc6._1, (BigInt(5) + mc6._2) + scr8)
        }
        (mc7._1, BigInt(5) + mc7._2)
    }
    (bd4._1, bd4._2)
  }
  
  def sorttime(l : List[BigInt]): (LList2, BigInt) = {
    val e15 = pullMintime(l)
    val scr6 = BigInt(1) + e15._2
    val bd1 = e15._1 match {
      case Cons(x, xs) =>
        (SCons1(x, Stream2(() => {
          val e18 = sorttime(xs)
          (e18._1, BigInt(1) + e18._2)
        })), BigInt(7) + scr6)
      case _ =>
        (SNil1(), BigInt(3) + scr6)
    }
    (bd1._1, bd1._2)
  }
  
  def concattime(l1 : List[BigInt], l2 : LList2): (LList2, BigInt) = {
    val bd6 = l1 match {
      case Cons(x, xs) =>
        (SCons1(x, Stream2(() => {
          val e48 = concattime(xs, l2)
          (e48._1, BigInt(1) + e48._2)
        })), BigInt(7))
      case Nil() =>
        (SNil1(), BigInt(4))
    }
    (bd6._1, bd6._2)
  }
  
  def kthMintime(l : Stream2, k : BigInt): (BigInt, BigInt) = {
    val lr = lookup[LList2](List(4878, l))
    val scr1 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e22 = Stream.listtime(l)
      (update[LList2](List(4878, l), e22._1), BigInt(1) + e22._2)
    }
    val bd2 = scr1._1 match {
      case SCons1(x, xs36) =>
        val mc2 = if (k == BigInt(1)) {
          (x, BigInt(2))
        } else {
          val e27 = kthMintime(xs36, k - BigInt(1))
          (e27._1, BigInt(4) + e27._2)
        }
        (mc2._1, (BigInt(4) + mc2._2) + scr1._2)
      case SNil1() =>
        (BigInt(0), BigInt(3) + scr1._2)
    }
    (bd2._1, bd2._2)
  }

   def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(2*x)).toList
    
    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      ops :+= {() => sorttime(input)._2}
      orb :+= {() => SortingnConcat0.sorttime0(input)._2}
    }
    run(size, ops, orb, "sort")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      // NOTE: floor take for coeff
      ops :+= {() => kthMintime(Stream2(()=>sorttime(input)), 10)._2}
      orb :+= {() => SortingnConcat0.kthMintime0(SortingnConcat0.Stream0(SortingnConcat0.SortL0(input)), 10, Set[SortingnConcat0.MemoFuns0]())._2}
    }
    run(size, ops, orb, "kthMintime")

  }
}

object LList {
  def size(thiss : SortingnConcat.LList2): BigInt = thiss match {
    case SortingnConcat.SCons1(_, t379) =>
      BigInt(1) + size(Star[SortingnConcat.LList2](Stream.listtime(t379)._1).*)
    case _ =>
      BigInt(0)
  }
}

object Stream {
  def listtime(thiss : SortingnConcat.Stream2): (SortingnConcat.LList2, BigInt) = {
    val e32 = thiss.lfun1()
    (e32._1, BigInt(2) + e32._2)
  }
  
  def size(thiss : SortingnConcat.Stream2): BigInt = LList.size(Star[SortingnConcat.LList2](listtime(thiss)._1).*)
}
