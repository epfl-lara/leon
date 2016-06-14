package StreamClient

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._
import StreamLibrary._

object StreamClient {
  def mapClienttime(n : BigInt): (BigInt, BigInt) = {
    val e123 = StreamLibrary.natsFromntime(BigInt(0))
    val e125 = StreamLibrary.maptime((n : BigInt) => {
      val e120 = StreamLibrary.constFun1time(n)
      (e120._1, e120._2)
    }, e123._1)
    val e127 = nthElemAfterMaptime(n, e125._1)
    (e127._1, ((BigInt(4) + e127._2) + e125._2) + e123._2)
  }
  
  def nthElemAfterMaptime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd10 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s107 @ StreamLibrary.SCons1(x, _) =>
        val mc7 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e64 = LList.tailOrNiltime(s107)
          val e66 = nthElemAfterMaptime(n - BigInt(1), e64._1)
          (e66._1, (BigInt(5) + e66._2) + e64._2)
        }
        (mc7._1, BigInt(4) + mc7._2)
    }
    (bd10._1, bd10._2)
  }
  
  def nthElemInRepeattime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd38 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s111 @ StreamLibrary.SCons1(x, _) =>
        val mc32 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e207 = LList.tailOrNiltime(s111)
          val e209 = nthElemInRepeattime(n - BigInt(1), e207._1)
          (e209._1, (BigInt(5) + e209._2) + e207._2)
        }
        (mc32._1, BigInt(4) + mc32._2)
    }
    (bd38._1, bd38._2)
  }
  
  def takeWhileClienttime(n : BigInt): (BigInt, BigInt) = {
    val e94 = StreamLibrary.natsFromntime(BigInt(0))
    val e96 = StreamLibrary.takeWhiletime((n : BigInt) => {
      val e91 = StreamLibrary.constFun2time(n)
      (e91._1, e91._2)
    }, e94._1)
    val e98 = nthElemAfterTakeWhiletime(n, e96._1)
    (e98._1, ((BigInt(4) + e98._2) + e96._2) + e94._2)
  }
  
  def nthElemAfterTakeWhiletime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd31 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s109 @ StreamLibrary.SCons1(x, _) =>
        val mc19 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e170 = LList.tailOrNiltime(s109)
          val e172 = nthElemAfterTakeWhiletime(n - BigInt(1), e170._1)
          (e172._1, (BigInt(5) + e172._2) + e170._2)
        }
        (mc19._1, BigInt(4) + mc19._2)
    }
    (bd31._1, bd31._2)
  }
  
  def scanClienttime(n : BigInt): (BigInt, BigInt) = {
    val e76 = StreamLibrary.natsFromntime(BigInt(0))
    val e78 = StreamLibrary.scantime((n : BigInt, m : BigInt) => {
      val e72 = StreamLibrary.constFun3time(n, m)
      (e72._1, e72._2)
    }, BigInt(0), e76._1)
    val e80 = nthElemAfterScantime(n, e78._1)
    (e80._1, ((BigInt(4) + e80._2) + e78._2) + e76._2)
  }
  
  def nthElemAfterScantime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd34 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s110 @ StreamLibrary.SCons1(x, _) =>
        val mc28 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e188 = LList.tailOrNiltime(s110)
          val e190 = nthElemAfterScantime(n - BigInt(1), e188._1)
          (e190._1, (BigInt(5) + e190._2) + e188._2)
        }
        (mc28._1, BigInt(4) + mc28._2)
    }
    (bd34._1, bd34._2)
  }
  
  def unfoldClienttime(n : BigInt, c : BigInt): (BigInt, BigInt) = {
    val e135 = StreamLibrary.unfoldtime((n : BigInt) => {
      val e132 = StreamLibrary.constFun4time(n)
      (e132._1, e132._2)
    }, c)
    val e137 = nthElemAfterUnfoldtime(n, e135._1)
    (e137._1, (BigInt(3) + e137._2) + e135._2)
  }
  
  def nthElemAfterUnfoldtime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd4 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s106 @ StreamLibrary.SCons1(x, _) =>
        val mc5 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e42 = LList.tailOrNiltime(s106)
          val e44 = nthElemAfterUnfoldtime(n - BigInt(1), e42._1)
          (e44._1, (BigInt(5) + e44._2) + e42._2)
        }
        (mc5._1, BigInt(4) + mc5._2)
    }
    (bd4._1, bd4._2)
  }
  
  def zipWithClienttime(n : BigInt): (BigInt, BigInt) = {
    val e20 = StreamLibrary.natsFromntime(BigInt(0))
    val e23 = StreamLibrary.natsFromntime(BigInt(0))
    val e25 = StreamLibrary.zipWithtime((n : BigInt, m : BigInt) => {
      val e17 = StreamLibrary.constFun3time(n, m)
      (e17._1, e17._2)
    }, e20._1, e23._1)
    val e27 = nthElemAfterZipWithtime(n, e25._1)
    (e27._1, (((BigInt(5) + e27._2) + e25._2) + e23._2) + e20._2)
  }
  
  def nthElemAfterZipWithtime(n : BigInt, s : StreamLibrary.LList2): (BigInt, BigInt) = {
    val bd18 = s match {
      case StreamLibrary.SNil1() =>
        (BigInt(0), BigInt(2))
      case s108 @ StreamLibrary.SCons1(x, _) =>
        val mc11 = if (n == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e113 = LList.tailOrNiltime(s108)
          val e115 = nthElemAfterZipWithtime(n - BigInt(1), e113._1)
          (e115._1, (BigInt(5) + e115._2) + e113._2)
        }
        (mc11._1, BigInt(4) + mc11._2)
    }
    (bd18._1, bd18._2)
  }
}
