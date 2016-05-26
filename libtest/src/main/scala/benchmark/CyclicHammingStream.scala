package CyclicHammingStream

import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._

object MergeAndHammingNumbers {
  
  case class SCons2(x321 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x320 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  @invisibleBody
  def maptime(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val bd6 = {
      val SCons2(x, _) = xs
      val e36 = f(x)
      (SCons2(e36._1, Susp1(() => {
        val e40 = mapSusptime(f, xs)
        (e40._1, BigInt(1) + e40._2)
      })), BigInt(7) + e36._2)
    }
    (bd6._1, bd6._2)
  }
  
  def mapSusptime(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val e102 = xs.tailFun1 match {
      case s84 @ Susp1(f133) =>
        val lr3 = lookup[SCons2](List(4912, s84))
        val mc9 = if (lr3._1) {
          (lr3._2, BigInt(1))
        } else {
          val e101 = ValOrSusp.fvaltime(s84)
          (update[SCons2](List(4912, s84), e101._1), BigInt(3) + e101._2)
        }
        (mc9._1, BigInt(4) + mc9._2)
      case Val1(x328) =>
        (x328, BigInt(5))
    }
    val e103 = maptime(f, e102._1)
    (e103._1, (BigInt(1) + e103._2) + e102._2)
  }
  
  def mintime(x : BigInt, y : BigInt, z : BigInt): (BigInt, BigInt) = {
    val bd12 = if (x <= y) {
      val th4 = if (x <= z) {
        (x, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (th4._1, BigInt(2) + th4._2)
    } else {
      val el5 = if (y <= z) {
        (y, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (el5._1, BigInt(2) + el5._2)
    }
    (bd12._1, bd12._2)
  }
  
  @invisibleBody
  def mergetime(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e25 = mintime(a.x321, b.x321, c.x321)
    (SCons2(e25._1, Susp1(() => {
      val e17 = mergeSusptime(a, b, c)
      (e17._1, BigInt(1) + e17._2)
    })), BigInt(8) + e25._2)
  }
  
  @invisibleBody
  def mergeSusptime(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e49 = mintime(a.x321, b.x321, c.x321)
    val e153 = e49._1
    val c25 = BigInt(2)
    val ir2 = if (a.x321 == e153) {
      val th = a.tailFun1 match {
        case s81 @ Susp1(f130) =>
          val lr = lookup[SCons2](List(4912, s81))
          val mc3 = if (lr._1) {
            (lr._2, BigInt(1))
          } else {
            val e52 = ValOrSusp.fvaltime(s81)
            (update[SCons2](List(4912, s81), e52._1), BigInt(3) + e52._2)
          }
          (mc3._1, BigInt(4) + mc3._2)
        case Val1(x325) =>
          (x325, BigInt(5))
      }
      (th._1, (BigInt(1) + c25) + th._2)
    } else {
      (a, BigInt(1) + c25)
    }
    val c27 = BigInt(2)
    val ir3 = if (b.x321 == e153) {
      val th1 = b.tailFun1 match {
        case s82 @ Susp1(f131) =>
          val lr1 = lookup[SCons2](List(4912, s82))
          val mc5 = if (lr1._1) {
            (lr1._2, BigInt(1))
          } else {
            val e58 = ValOrSusp.fvaltime(s82)
            (update[SCons2](List(4912, s82), e58._1), BigInt(3) + e58._2)
          }
          (mc5._1, BigInt(4) + mc5._2)
        case Val1(x326) =>
          (x326, BigInt(5))
      }
      (th1._1, (BigInt(1) + c27) + th1._2)
    } else {
      (b, BigInt(1) + c27)
    }
    val c29 = BigInt(2)
    val ir4 = if (c.x321 == e153) {
      val th2 = c.tailFun1 match {
        case s83 @ Susp1(f132) =>
          val lr2 = lookup[SCons2](List(4912, s83))
          val mc7 = if (lr2._1) {
            (lr2._2, BigInt(1))
          } else {
            val e64 = ValOrSusp.fvaltime(s83)
            (update[SCons2](List(4912, s83), e64._1), BigInt(3) + e64._2)
          }
          (mc7._1, BigInt(4) + mc7._2)
        case Val1(x327) =>
          (x327, BigInt(5))
      }
      (th2._1, (BigInt(1) + c29) + th2._2)
    } else {
      (c, BigInt(1) + c29)
    }
    val e71 = mergetime(ir2._1, ir3._1, ir4._1)
    (e71._1, ((((BigInt(9) + e71._2) + ir4._2) + ir3._2) + ir2._2) + e49._2)
  }
  
  val hamstreamtime : (SCons2, BigInt) = (SCons2(BigInt(1), Susp1(() => {
    val e31 = hamGentime
    (e31._1, BigInt(1) + e31._2)
  })), BigInt(3))
  
  @invisibleBody
  def hamGentime(): (SCons2, BigInt) = {
    val e104 = hamstreamtime._1
    val e77 = maptime((x$2 : BigInt) => (BigInt(2) * x$2, BigInt(1)), e104)
    val e83 = maptime((x$3 : BigInt) => (BigInt(3) * x$3, BigInt(1)), e104)
    val e89 = maptime((x$4 : BigInt) => (BigInt(5) * x$4, BigInt(1)), e104)
    val e91 = mergetime(e77._1, e83._1, e89._1)
    (e91._1, (((BigInt(9) + e91._2) + e89._2) + e83._2) + e77._2)
  }
  
}

object SCons {
  
}

object ValOrSusp {
  def fvaltime(thiss : MergeAndHammingNumbers.ValOrSusp2): (MergeAndHammingNumbers.SCons2, BigInt) = {
    val bd2 = thiss match {
      case MergeAndHammingNumbers.Susp1(f129) =>
        val e29 = f129()
        (e29._1, BigInt(4) + e29._2)
      case MergeAndHammingNumbers.Val1(x324) =>
        (x324, BigInt(4))
    }
    (bd2._1, bd2._2)
  }
}
