package withOrb
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._

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
