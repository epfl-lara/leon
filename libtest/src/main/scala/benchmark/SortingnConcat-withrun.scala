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
  
  case class Stream0(lfun1 : tLList0)
  
  def pullMintime0(l39 : List[BigInt]): (List[BigInt], BigInt) = {
    val bd5 = l39 match {
      case Nil() =>
        (l39, BigInt(2))
      case Cons(x15, xs2) =>
        val e66 = pullMintime0(xs2)
        val scr8 = BigInt(1) + e66._2
        val mc11 = e66._1 match {
          case Nil0() =>
            (Cons[BigInt](x15, Nil0[BigInt]()), BigInt(4) + scr8)
          case nxs0 @ Cons(y6, ys0) =>
            val mc10 = if (x15 <= y6) {
              (Cons[BigInt](x15, nxs0), BigInt(3))
            } else {
              (Cons[BigInt](y6, Cons0[BigInt](x15, ys0)), BigInt(4))
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
  
  abstract class tLList0
  
  case class SortL0(xs36 : List[BigInt]) extends tLList0
  
  case class ConcatL0(xs37 : List0[BigInt], l215 : LList0) extends tLList0
  
  abstract class MemoFuns0
  
  case class List-memM0(thiss634 : Stream0) extends MemoFuns0

  def uiState4(): Set[MemoFuns0] = (_ : Set[MemoFuns0])
}

object LList1 {
  def size15(thiss635 : LList0): BigInt = thiss635 match {
    case SCons0(_, t8) =>
      BigInt(1) + t8.listmemtime0(uiState4)._1._1.size15
    case _ =>
      BigInt(0)
  }
}

object Stream1 {
  def listmemtime0(thiss636 : Stream0, st5 : Set[MemoFuns0]): ((LList0, Set[MemoFuns0]), BigInt) = {
    val e57 = evaltLListtime0(thiss636.lfun1)
    ((e57._1, st5), BigInt(3) + e57._2)
  }
  
  def listmemUI0(thiss637 : Stream0): LList0 = (_ : LList0)
  
  @axiom
  def listmemValPred0(thiss638 : Stream0, valres3 : LList0): Boolean = valres3 == listmemUI0(thiss638)
}
