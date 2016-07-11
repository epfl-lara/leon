package CyclicHammingStream

import leon.collection._
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
  def mapalloc(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val bd13 = {
      val SCons2(x, _) = xs
      val e99 = f(x)
      (SCons2(e99._1, Susp1(() => {
        val e103 = mapSuspalloc(f, xs)
        (e103._1, e103._2)
      })), BigInt(2) + e99._2)
    }
    (bd13._1, bd13._2)
  }
  
  def mapSuspalloc(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val e130 = xs.tailFun1 match {
      case s82 @ Susp1(f132) =>
        val lr3 = lookup[SCons2](List(4931, s82))
        val mc10 = if (lr3._1) {
          (lr3._2, BigInt(0))
        } else {
          val e129 = ValOrSusp.fvalalloc(s82)
          (update[SCons2](List(4931, s82), e129._1), e129._2)
        }
        (mc10._1, mc10._2)
      case Val1(x326) =>
        (x326, BigInt(0))
    }
    val e131 = mapalloc(f, e130._1)
    (e131._1, e131._2 + e130._2)
  }
  
  def minalloc(x : BigInt, y : BigInt, z : BigInt): (BigInt, BigInt) = {
    val bd15 = if (x <= y) {
      val th7 = if (x <= z) {
        (x, BigInt(0))
      } else {
        (z, BigInt(0))
      }
      (th7._1, th7._2)
    } else {
      val el8 = if (y <= z) {
        (y, BigInt(0))
      } else {
        (z, BigInt(0))
      }
      (el8._1, el8._2)
    }
    (bd15._1, bd15._2)
  }
  
  @invisibleBody
  def mergealloc(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e94 = minalloc(a.x321, b.x321, c.x321)
    (SCons2(e94._1, Susp1(() => {
      val e86 = mergeSuspalloc(a, b, c)
      (e86._1, e86._2)
    })), BigInt(2) + e94._2)
  }
  
  @invisibleBody
  def forcealloc(a : SCons2): (SCons2, BigInt) = {
    val bd5 = a.tailFun1 match {
      case s79 @ Susp1(f129) =>
        val lr = lookup[SCons2](List(4931, s79))
        val mc2 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e38 = ValOrSusp.fvalalloc(s79)
          (update[SCons2](List(4931, s79), e38._1), e38._2)
        }
        (mc2._1, mc2._2)
      case Val1(x323) =>
        (x323, BigInt(0))
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def mergeSuspalloc(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e45 = minalloc(a.x321, b.x321, c.x321)
    val e163 = e45._1
    val ir2 = if (a.x321 == e163) {
      val e47 = forcealloc(a)
      (e47._1, e47._2)
    } else {
      (a, BigInt(0))
    }
    val ir3 = if (b.x321 == e163) {
      val e52 = forcealloc(b)
      (e52._1, e52._2)
    } else {
      (b, BigInt(0))
    }
    val ir4 = if (c.x321 == e163) {
      val e57 = forcealloc(c)
      (e57._1, e57._2)
    } else {
      (c, BigInt(0))
    }
    val e64 = mergealloc(ir2._1, ir3._1, ir4._1)
    (e64._1, (((e64._2 + ir4._2) + ir3._2) + ir2._2) + e45._2)
  }
  
  @invisibleBody
  def nextalloc(f : SCons2, s : SCons2): (SCons2, BigInt) = {
    val bd16 = s.tailFun1 match {
      case s81 @ Susp1(f131) =>
        val lr2 = lookup[SCons2](List(4931, s81))
        val mc8 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e125 = ValOrSusp.fvalalloc(s81)
          (update[SCons2](List(4931, s81), e125._1), e125._2)
        }
        (mc8._1, mc8._2)
      case Val1(x325) =>
        (x325, BigInt(0))
    }
    (bd16._1, bd16._2)
  }
  
  @invisibleBody
  def nthElemAfterSecondalloc(n : BigInt, f : SCons2, s : SCons2): (BigInt, BigInt) = {
    val e108 = nextalloc(f, s)
    val bd14 = {
      val t370 @ SCons2(x, _) = e108._1
      val mc7 = if (n == BigInt(2)) {
        (x, BigInt(0))
      } else {
        val e114 = nthElemAfterSecondalloc(n - BigInt(1), s, t370)
        (e114._1, e114._2)
      }
      (mc7._1, mc7._2 + e108._2)
    }
    (bd14._1, bd14._2)
  }
  
  val hamstreamalloc : (SCons2, BigInt) = (SCons2(BigInt(1), Susp1(() => {
    val e66 = hamGenalloc
    (e66._1, e66._2)
  })), BigInt(2))
  
  @invisibleBody
  def hamGenalloc(): (SCons2, BigInt) = {
    val e138 = hamstreamalloc._1
    val e21 = mapalloc((x$6 : BigInt) => (BigInt(2) * x$6, BigInt(0)), e138)
    val e27 = mapalloc((x$7 : BigInt) => (BigInt(3) * x$7, BigInt(0)), e138)
    val e33 = mapalloc((x$8 : BigInt) => (BigInt(5) * x$8, BigInt(0)), e138)
    val e35 = mergealloc(e21._1, e27._1, e33._1)
    (e35._1, ((e35._2 + e33._2) + e27._2) + e21._2)
  }
  
  def nthHammingNumberalloc(n : BigInt): (BigInt, BigInt) = {
    val e194 = hamstreamalloc._1
    val r164 = if (n == BigInt(0)) {
      (e194.x321, BigInt(0))
    } else {
      val ir6 = e194.tailFun1 match {
        case s80 @ Susp1(f130) =>
          val lr1 = lookup[SCons2](List(4931, s80))
          val mc4 = if (lr1._1) {
            (lr1._2, BigInt(0))
          } else {
            val e73 = ValOrSusp.fvalalloc(s80)
            (update[SCons2](List(4931, s80), e73._1), e73._2)
          }
          (mc4._1, mc4._2)
        case Val1(x324) =>
          (x324, BigInt(0))
      }
      val r163 = if (n == BigInt(1)) {
        (ir6._1.x321, BigInt(0))
      } else {
        val e78 = nthElemAfterSecondalloc(n, e194, ir6._1)
        (e78._1, e78._2)
      }
      (r163._1, r163._2 + ir6._2)
    }
    (r164._1, r164._2)
  }
  
}

object SCons {
  
}

object ValOrSusp {
  def fvalalloc(thiss : MergeAndHammingNumbers.ValOrSusp2): (MergeAndHammingNumbers.SCons2, BigInt) = {
    val bd = thiss match {
      case MergeAndHammingNumbers.Susp1(f128) =>
        val e15 = f128()
        (e15._1, e15._2)
      case MergeAndHammingNumbers.Val1(x322) =>
        (x322, BigInt(0))
    }
    (bd._1, bd._2)
  }
}
