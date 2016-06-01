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
import leon.runtimeDriver._

object MergeAndHammingNumbers {
  
  case class SCons2(x321 : BigInt, tailFun1 : ValOrSusp2) {
    @inline
    def tail = tailFun1 match {
      case s@Susp1(f) => s.fun1()._1
      case Val1(x) => x
    }
  }
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x320 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  @invisibleBody
  def maptime(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val bd13 = {
      val SCons2(x, _) = xs
      val e99 = f(x)
      (SCons2(e99._1, Susp1(() => {
        val e103 = mapSusptime(f, xs)
        (e103._1, BigInt(1) + e103._2)
      })), BigInt(7) + e99._2)
    }
    (bd13._1, bd13._2)
  }
  
  def mapSusptime(f : (BigInt) => (BigInt, BigInt), xs : SCons2): (SCons2, BigInt) = {
    val e130 = xs.tailFun1 match {
      case s82 @ Susp1(f131) =>
        val lr3 = lookup[SCons2](List(4927, s82))
        val mc10 = if (lr3._1) {
          (lr3._2, BigInt(1))
        } else {
          val e129 = ValOrSusp.fvaltime(s82)
          (update[SCons2](List(4927, s82), e129._1), BigInt(3) + e129._2)
        }
        (mc10._1, BigInt(4) + mc10._2)
      case Val1(x326) =>
        (x326, BigInt(5))
    }
    val e131 = maptime(f, e130._1)
    (e131._1, (BigInt(1) + e131._2) + e130._2)
  }
  
  def mintime(x : BigInt, y : BigInt, z : BigInt): (BigInt, BigInt) = {
    val bd15 = if (x <= y) {
      val th7 = if (x <= z) {
        (x, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (th7._1, BigInt(2) + th7._2)
    } else {
      val el8 = if (y <= z) {
        (y, BigInt(2))
      } else {
        (z, BigInt(2))
      }
      (el8._1, BigInt(2) + el8._2)
    }
    (bd15._1, bd15._2)
  }
  
  @invisibleBody
  def mergetime(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e94 = mintime(a.x321, b.x321, c.x321)
    (SCons2(e94._1, Susp1(() => {
      val e86 = mergeSusptime(a, b, c)
      (e86._1, BigInt(1) + e86._2)
    })), BigInt(7) + e94._2)
  }
  
  @invisibleBody
  def forcetime(a : SCons2): (SCons2, BigInt) = {
    val bd4 = a.tailFun1 match {
      case s79 @ Susp1(f127) =>
        val lr = lookup[SCons2](List(4927, s79))
        val mc = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e36 = ValOrSusp.fvaltime(s79)
          (update[SCons2](List(4927, s79), e36._1), BigInt(3) + e36._2)
        }
        (mc._1, BigInt(4) + mc._2)
      case Val1(x322) =>
        (x322, BigInt(5))
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def mergeSusptime(a : SCons2, b : SCons2, c : SCons2): (SCons2, BigInt) = {
    val e43 = mintime(a.x321, b.x321, c.x321)
    val e138 = e43._1
    val c22 = BigInt(2)
    val ir2 = if (a.x321 == e138) {
      val e45 = forcetime(a)
      (e45._1, (BigInt(2) + c22) + e45._2)
    } else {
      (a, BigInt(1) + c22)
    }
    val c24 = BigInt(2)
    val ir3 = if (b.x321 == e138) {
      val e50 = forcetime(b)
      (e50._1, (BigInt(2) + c24) + e50._2)
    } else {
      (b, BigInt(1) + c24)
    }
    val c26 = BigInt(2)
    val ir4 = if (c.x321 == e138) {
      val e55 = forcetime(c)
      (e55._1, (BigInt(2) + c26) + e55._2)
    } else {
      (c, BigInt(1) + c26)
    }
    val e62 = mergetime(ir2._1, ir3._1, ir4._1)
    (e62._1, ((((BigInt(5) + e62._2) + ir4._2) + ir3._2) + ir2._2) + e43._2)
  }
  
  @invisibleBody
  def nexttime(f : SCons2, s : SCons2): (SCons2, BigInt) = {
    val bd16 = s.tailFun1 match {
      case s81 @ Susp1(f130) =>
        val lr2 = lookup[SCons2](List(4927, s81))
        val mc8 = if (lr2._1) {
          (lr2._2, BigInt(1))
        } else {
          val e125 = ValOrSusp.fvaltime(s81)
          (update[SCons2](List(4927, s81), e125._1), BigInt(3) + e125._2)
        }
        (mc8._1, BigInt(4) + mc8._2)
      case Val1(x325) =>
        (x325, BigInt(5))
    }
    (bd16._1, bd16._2)
  }
  
  @invisibleBody
  def nthElemAfterSecondtime(n : BigInt, f : SCons2, s : SCons2): (BigInt, BigInt) = {
    val e108 = nexttime(f, s)
    val bd14 = {
      val t370 @ SCons2(x, _) = e108._1
      val mc7 = if (n == BigInt(2)) {
        (x, BigInt(2))
      } else {
        val e114 = nthElemAfterSecondtime(n - BigInt(1), s, t370)
        (e114._1, BigInt(4) + e114._2)
      }
      (mc7._1, (BigInt(4) + mc7._2) + e108._2)
    }
    (bd14._1, bd14._2)
  }
  
  val hamstreamtime : (SCons2, BigInt) = (SCons2(BigInt(1), Susp1(() => {
    val e66 = hamGentime
    (e66._1, BigInt(1) + e66._2)
  })), BigInt(3))
  
  @invisibleBody
  def hamGentime(): (SCons2, BigInt) = {
    val e154 = hamstreamtime._1
    val e19 = maptime((x$6 : BigInt) => (BigInt(2) * x$6, BigInt(1)), e154)
    val e25 = maptime((x$7 : BigInt) => (BigInt(3) * x$7, BigInt(1)), e154)
    val e31 = maptime((x$8 : BigInt) => (BigInt(5) * x$8, BigInt(1)), e154)
    val e33 = mergetime(e19._1, e25._1, e31._1)
    (e33._1, (((BigInt(8) + e33._2) + e31._2) + e25._2) + e19._2)
  }
  
  def nthHammingNumbertime(n : BigInt): (BigInt, BigInt) = {
    val e186 = hamstreamtime._1
    val r164 = if (n == BigInt(0)) {
      (e186.x321, BigInt(3))
    } else {
      val ir6 = e186.tailFun1 match {
        case s80 @ Susp1(f129) =>
          val lr1 = lookup[SCons2](List(4927, s80))
          val mc4 = if (lr1._1) {
            (lr1._2, BigInt(1))
          } else {
            val e73 = ValOrSusp.fvaltime(s80)
            (update[SCons2](List(4927, s80), e73._1), BigInt(3) + e73._2)
          }
          (mc4._1, BigInt(4) + mc4._2)
        case Val1(x324) =>
          (x324, BigInt(5))
      }
      val r163 = if (n == BigInt(1)) {
        (ir6._1.x321, BigInt(3))
      } else {
        val e78 = nthElemAfterSecondtime(n, e186, ir6._1)
        (e78._1, BigInt(3) + e78._2)
      }
      (r163._1, (BigInt(2) + r163._2) + ir6._2)
    }
    (r164._1, BigInt(1) + r164._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000) // can change this
    val size = points.map(x => BigInt(x)).toList
    
    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {() => {
          leon.mem.clearMemo()
          nthHammingNumbertime(input)._2
        }
      }
      orb :+= {() => (123*(input) + 4)}
      
    }
    plot(size, ops, orb, "nthHammingNumber", "orb")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      val hamstreamf = hamstreamtime._1
      val hamstreams = hamstreamf.tail
      ops :+= {() => {
          leon.mem.clearMemo()
          nthElemAfterSecondtime(input, hamstreamf, hamstreams)._2
        }
      }
      orb :+= {() => (123*(input) - 121)}
      
    }
    plot(size, ops, orb, "nthElemAfterSecondHam", "orb")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      val hamstreamf = hamstreamtime._1
      val hamstreams = hamstreamf.tail
      ops :+= {() => {
          leon.mem.clearMemo()
          nexttime(hamstreamf, hamstreams)._2
        }
      }
      orb :+= {() => (115)}
      
    }
    plot(size, ops, orb, "nextHam", "orb")


    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      val hamstreamf = hamstreamtime._1
      val hamstreams = hamstreamf.tail
      val hamstreamt = hamstreams.tail
      ops :+= {() => {
          leon.mem.clearMemo()
          mergetime(hamstreamf, hamstreams, hamstreamt)._2
        }
      }
      orb :+= {() => (11)}
      
    }
    plot(size, ops, orb, "mergeHam", "orb")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      val hamstreamf = hamstreamtime._1
      val hamstreams = hamstreamf.tail
      val hamstreamt = hamstreams.tail
      ops :+= {() => {
          leon.mem.clearMemo()
          mergeSusptime(hamstreamf, hamstreams, hamstreamt)._2
        }
      }
      orb :+= {() => (104)}
      
    }
    plot(size, ops, orb, "mergeSuspHam", "orb")
  }
  
}

object SCons {
  
}

object ValOrSusp {
  def fvaltime(thiss : MergeAndHammingNumbers.ValOrSusp2): (MergeAndHammingNumbers.SCons2, BigInt) = {
    val bd6 = thiss match {
      case MergeAndHammingNumbers.Susp1(f128) =>
        val e64 = f128()
        (e64._1, BigInt(4) + e64._2)
      case MergeAndHammingNumbers.Val1(x323) =>
        (x323, BigInt(4))
    }
    (bd6._1, bd6._2)
  }
}
