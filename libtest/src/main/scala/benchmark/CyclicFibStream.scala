package CyclicFibStream

import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._

object ZipWithAndFibStream {
  
  case class SCons2(x320 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x319 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  def zipWithFuntime(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val bd3 = {
      val (SCons2(x, _), SCons2(y, _)) = (xs, ys)
      val e31 = f(x, y)
      (SCons2(e31._1, Susp1(() => {
        val e36 = zipWithSusptime(f, xs, ys)
        (e36._1, BigInt(1) + e36._2)
      })), BigInt(13) + e31._2)
    }
    (bd3._1, bd3._2)
  }
  
  def zipWithSusptime(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val e20 = xs.tailFun1 match {
      case s82 @ Susp1(f131) =>
        val lr = lookup[SCons2](List(4903, s82))
        val mc2 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e19 = ValOrSusp.fvaltime(s82)
          (update[SCons2](List(4903, s82), e19._1), BigInt(3) + e19._2)
        }
        (mc2._1, BigInt(4) + mc2._2)
      case Val1(x325) =>
        (x325, BigInt(5))
    }
    val e24 = ys.tailFun1 match {
      case s83 @ Susp1(f132) =>
        val lr1 = lookup[SCons2](List(4903, s83))
        val mc4 = if (lr1._1) {
          (lr1._2, BigInt(1))
        } else {
          val e23 = ValOrSusp.fvaltime(s83)
          (update[SCons2](List(4903, s83), e23._1), BigInt(3) + e23._2)
        }
        (mc4._1, BigInt(4) + mc4._2)
      case Val1(x326) =>
        (x326, BigInt(5))
    }
    val e25 = zipWithFuntime(f, e20._1, e24._1)
    (e25._1, ((BigInt(1) + e25._2) + e24._2) + e20._2)
  }
  
  val fibstreamtime : (SCons2, BigInt) = (SCons2(BigInt(0), Val1(SCons2(BigInt(1), Susp1(() => (genNexttime._1, BigInt(1)))))), BigInt(5))
  
  @invisibleBody
  val genNexttime : (SCons2, BigInt) = {
    val e80 = fibstreamtime._1
    val e54 = e80.tailFun1 match {
      case s84 @ Susp1(f133) =>
        val lr2 = lookup[SCons2](List(4903, s84))
        val mc7 = if (lr2._1) {
          (lr2._2, BigInt(1))
        } else {
          val e53 = ValOrSusp.fvaltime(s84)
          (update[SCons2](List(4903, s84), e53._1), BigInt(3) + e53._2)
        }
        (mc7._1, BigInt(4) + mc7._2)
      case Val1(x327) =>
        (x327, BigInt(5))
    }
    val e55 = zipWithSusptime((x$1 : BigInt, x$2 : BigInt) => (x$1 + x$2, BigInt(1)), e80, e54._1)
    (e55._1, (BigInt(4) + e55._2) + e54._2)
  }
  
}

object SCons {
  
}

object ValOrSusp {
  def fvaltime(thiss : ZipWithAndFibStream.ValOrSusp2): (ZipWithAndFibStream.SCons2, BigInt) = {
    val bd = thiss match {
      case ZipWithAndFibStream.Susp1(f128) =>
        val e15 = f128()
        (e15._1, BigInt(4) + e15._2)
      case ZipWithAndFibStream.Val1(x322) =>
        (x322, BigInt(4))
    }
    (bd._1, bd._2)
  }
}
