package Deque

import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.math._
import leon.invariant._
import leon.runtimeDriver._

object RealTimeDeque {
  
  abstract class Stream2[T]
  
  
  case class SCons1[T](x442 : T, next64 : ValOrFun2[T]) extends Stream2[T]
  
  
  case class SNil1[T]() extends Stream2[T]
  
  
  abstract class ValOrFun2[T]
  
  
  case class Val1[T](x440 : Stream2[T]) extends ValOrFun2[T]
  
  
  case class Fun3[T](fun23 : () => (Stream2[T], BigInt)) extends ValOrFun2[T]
  
  
  case class Queue2[T](f227 : Stream2[T], lenf77 : BigInt, sf75 : Stream2[T], r238 : Stream2[T], lenr77 : BigInt, sr75 : Stream2[T])
  
  @invstate
  def takeLazytime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd14 = {
      val c45 @ SCons1(x, _) = l
      val mc28 = if (n == BigInt(1)) {
        (SCons1[T](x, Val1[T](SNil1[T]())), BigInt(5))
      } else {
        val ir36 = n - BigInt(1)
        val ir21 = c45 match {
          case SCons1(_, Val1(x616)) =>
            (x616, BigInt(5))
          case SCons1(_, f350 @ Fun3(_)) =>
            val lr6 = lookup[Stream2[T]](List(6118, f350))
            val mc27 = if (lr6._1) {
              (lr6._2, BigInt(1))
            } else {
              val e222 = ValOrFun.gettime[T](f350)
              (update[Stream2[T]](List(6118, f350), e222._1), BigInt(3) + e222._2)
            }
            (mc27._1, BigInt(7) + mc27._2)
        }
        (SCons1[T](x, Fun3[T](() => {
          val e226 = takeLazytime[T](ir36, ir21._1)
          (e226._1, BigInt(1) + e226._2)
        })), BigInt(6) + ir21._2)
      }
      (mc28._1, BigInt(3) + mc28._2)
    }
    (bd14._1, bd14._2)
  }
  
  @invstate
  def revAppendtime[T](l1 : Stream2[T], l2 : Stream2[T]): (Stream2[T], BigInt) = {
    val bd10 = l1 match {
      case SNil1() =>
        (l2, BigInt(2))
      case c39 @ SCons1(x, _) =>
        val e189 = c39 match {
          case SCons1(_, Val1(x567)) =>
            (x567, BigInt(5))
          case SCons1(_, f342 @ Fun3(_)) =>
            val lr4 = lookup[Stream2[T]](List(6118, f342))
            val mc20 = if (lr4._1) {
              (lr4._2, BigInt(1))
            } else {
              val e188 = ValOrFun.gettime[T](f342)
              (update[Stream2[T]](List(6118, f342), e188._1), BigInt(3) + e188._2)
            }
            (mc20._1, BigInt(7) + mc20._2)
        }
        val e194 = revAppendtime[T](e189._1, SCons1[T](x, Val1[T](l2)))
        (e194._1, (BigInt(7) + e194._2) + e189._2)
    }
    (bd10._1, bd10._2)
  }
  
  @invstate
  def droptime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd9 = if (n == BigInt(0)) {
      (l, BigInt(2))
    } else {
      val el3 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c38 @ SCons1(x, _) =>
          val e183 = c38 match {
            case SCons1(_, Val1(x560)) =>
              (x560, BigInt(5))
            case SCons1(_, f340 @ Fun3(_)) =>
              val lr3 = lookup[Stream2[T]](List(6118, f340))
              val mc16 = if (lr3._1) {
                (lr3._2, BigInt(1))
              } else {
                val e182 = ValOrFun.gettime[T](f340)
                (update[Stream2[T]](List(6118, f340), e182._1), BigInt(3) + e182._2)
              }
              (mc16._1, BigInt(7) + mc16._2)
          }
          val e184 = droptime[T](n - BigInt(1), e183._1)
          (e184._1, (BigInt(6) + e184._2) + e183._2)
      }
      (el3._1, BigInt(2) + el3._2)
    }
    (bd9._1, bd9._2)
  }
  
  @invstate
  def taketime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd15 = if (n == BigInt(0)) {
      (SNil1[T](), BigInt(3))
    } else {
      val el5 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c48 @ SCons1(x, _) =>
          val e237 = c48 match {
            case SCons1(_, Val1(x624)) =>
              (x624, BigInt(5))
            case SCons1(_, f352 @ Fun3(_)) =>
              val lr7 = lookup[Stream2[T]](List(6118, f352))
              val mc31 = if (lr7._1) {
                (lr7._2, BigInt(1))
              } else {
                val e236 = ValOrFun.gettime[T](f352)
                (update[Stream2[T]](List(6118, f352), e236._1), BigInt(3) + e236._2)
              }
              (mc31._1, BigInt(7) + mc31._2)
          }
          val e238 = taketime[T](n - BigInt(1), e237._1)
          (SCons1[T](x, Val1[T](e238._1)), (BigInt(8) + e238._2) + e237._2)
      }
      (el5._1, BigInt(2) + el5._2)
    }
    (bd15._1, bd15._2)
  }
  
  @invstate
  def rotateRevtime[T](r : Stream2[T], f : Stream2[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd12 = r match {
      case SNil1() =>
        val e197 = revAppendtime[T](f, a)
        (e197._1, BigInt(3) + e197._2)
      case c41 @ SCons1(x, _) =>
        val ir17 = c41 match {
          case SCons1(_, Val1(x584)) =>
            (x584, BigInt(5))
          case SCons1(_, f345 @ Fun3(_)) =>
            val lr5 = lookup[Stream2[T]](List(6118, f345))
            val mc24 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e199 = ValOrFun.gettime[T](f345)
              (update[Stream2[T]](List(6118, f345), e199._1), BigInt(3) + e199._2)
            }
            (mc24._1, BigInt(7) + mc24._2)
        }
        val e202 = droptime[T](BigInt(2), f)
        val e411 = e202._1
        val e205 = taketime[T](BigInt(2), f)
        val e208 = revAppendtime[T](e205._1, a)
        val e417 = e208._1
        (SCons1[T](x, Fun3[T](() => {
          val e213 = rotateRevtime[T](ir17._1, e411, e417)
          (e213._1, BigInt(1) + e213._2)
        })), (((BigInt(10) + e208._2) + e205._2) + e202._2) + ir17._2)
    }
    (bd12._1, bd12._2)
  }
  
  @invstate
  def rotateDroptime[T](r : Stream2[T], i : BigInt, f : Stream2[T]): (Stream2[T], BigInt) = {
    val c56 = BigInt(4)
    val bd6 = if (i < BigInt(2) || r == SNil1[T]()) {
      val e109 = droptime[T](i, f)
      val e112 = rotateRevtime[T](r, e109._1, SNil1[T]())
      (e112._1, ((BigInt(4) + c56) + e112._2) + e109._2)
    } else {
      val el2 = {
        val c32 @ SCons1(x, _) = r
        val ir12 = c32 match {
          case SCons1(_, Val1(x527)) =>
            (x527, BigInt(5))
          case SCons1(_, f308 @ Fun3(_)) =>
            val lr2 = lookup[Stream2[T]](List(6118, f308))
            val mc12 = if (lr2._1) {
              (lr2._2, BigInt(1))
            } else {
              val e114 = ValOrFun.gettime[T](f308)
              (update[Stream2[T]](List(6118, f308), e114._1), BigInt(3) + e114._2)
            }
            (mc12._1, BigInt(7) + mc12._2)
        }
        val ir24 = i - BigInt(2)
        val e119 = droptime[T](BigInt(2), f)
        val e314 = e119._1
        (SCons1[T](x, Fun3[T](() => {
          val e124 = rotateDroptime[T](ir12._1, ir24, e314)
          (e124._1, BigInt(1) + e124._2)
        })), (BigInt(8) + e119._2) + ir12._2)
      }
      (el2._1, (BigInt(1) + c56) + el2._2)
    }
    (bd6._1, bd6._2)
  }
  
  @invisibleBody
  def createQueuetime[T](f : Stream2[T], lenf : BigInt, sf : Stream2[T], r : Stream2[T], lenr : BigInt, sr : Stream2[T]): (Queue2[T], BigInt) = {
    val c62 = BigInt(3)
    val bd3 = if (lenf > BigInt(1) + BigInt(2) * lenr) {
      val ir43 = (lenf + lenr) / BigInt(2)
      val e35 = rotateDroptime[T](r, ir43, f)
      val e427 = e35._1
      val e38 = takeLazytime[T](ir43, f)
      val e429 = e38._1
      (Queue2[T](e429, ir43, e429, e427, (lenf + lenr) - ir43, e427), ((BigInt(8) + c62) + e38._2) + e35._2)
    } else {
      val c64 = BigInt(3)
      val el1 = if (lenr > BigInt(1) + BigInt(2) * lenf) {
        val ir51 = (lenf + lenr) / BigInt(2)
        val ir53 = (lenf + lenr) - ir51
        val e56 = rotateDroptime[T](f, ir53, r)
        val e439 = e56._1
        val e59 = takeLazytime[T](ir53, r)
        val e441 = e59._1
        (Queue2[T](e439, ir51, e439, e441, ir53, e441), ((BigInt(8) + c64) + e59._2) + e56._2)
      } else {
        (Queue2[T](f, lenf, sf, r, lenr, sr), BigInt(2) + c64)
      }
      (el1._1, (BigInt(1) + c62) + el1._2)
    }
    (bd3._1, bd3._2)
  }
  
  @invisibleBody
  def forcetime[T](tar : Stream2[T], htar : Stream2[T], other : Stream2[T], hother : Stream2[T]): (Stream2[T], BigInt) = {
    val bd1 = tar match {
      case c21 @ SCons1(_, _) =>
        val mc4 = c21 match {
          case SCons1(_, Val1(x465)) =>
            (x465, BigInt(5))
          case SCons1(_, f257 @ Fun3(_)) =>
            val lr = lookup[Stream2[T]](List(6118, f257))
            val mc3 = if (lr._1) {
              (lr._2, BigInt(1))
            } else {
              val e17 = ValOrFun.gettime[T](f257)
              (update[Stream2[T]](List(6118, f257), e17._1), BigInt(3) + e17._2)
            }
            (mc3._1, BigInt(7) + mc3._2)
        }
        (mc4._1, BigInt(2) + mc4._2)
      case _ =>
        (tar, BigInt(2))
    }
    (bd1._1, bd1._2)
  }
  
  @invisibleBody
  def forceTwicetime[T](q : Queue2[T]): ((Stream2[T], Stream2[T]), BigInt) = {
    val e262 = forcetime[T](q.sf75, q.f227, q.r238, q.sr75)
    val e270 = forcetime[T](e262._1, q.f227, q.r238, q.sr75)
    val e346 = e270._1
    val e278 = forcetime[T](q.sr75, q.r238, q.f227, e346)
    val e285 = forcetime[T](e278._1, q.r238, q.f227, e346)
    ((e346, e285._1), (((BigInt(17) + e285._2) + e278._2) + e270._2) + e262._2)
  }
  
  def emptytime[T](): (Queue2[T], BigInt) = {
    val ir38 = SNil1[T]()
    (Queue2[T](ir38, BigInt(0), ir38, ir38, BigInt(0), ir38), BigInt(2))
  }
  
  def constime[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val e141 = forcetime[T](q.sf75, q.f227, q.r238, q.sr75)
    val e372 = e141._1
    val e149 = forcetime[T](q.sr75, q.r238, q.f227, e372)
    val e165 = createQueuetime[T](SCons1[T](x, Val1[T](q.f227)), BigInt(1) + q.lenf77, e372, q.r238, q.lenr77, e149._1)
    (e165._1, ((BigInt(17) + e165._2) + e149._2) + e141._2)
  }
  
  def tailtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val e251 = forcetime[T](q.f227, q.sf75, q.r238, q.sr75)
    val bd16 = {
      val _ = e251._1
      val e253 = tailSubtime[T](q)
      (e253._1, (BigInt(7) + e253._2) + e251._2)
    }
    (bd16._1, bd16._2)
  }
  
  def tailSubtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd4 = q.f227 match {
      case c28 @ SCons1(x, _) =>
        val e86 = forceTwicetime[T](q)
        val ir9 = {
          val (nsf, nsr) = e86._1
          ((nsf, nsr), BigInt(6) + e86._2)
        }
        val ir59 = ir9._1
        val e93 = c28 match {
          case SCons1(_, Val1(x505)) =>
            (x505, BigInt(5))
          case SCons1(_, f288 @ Fun3(_)) =>
            val lr1 = lookup[Stream2[T]](List(6118, f288))
            val mc8 = if (lr1._1) {
              (lr1._2, BigInt(1))
            } else {
              val e92 = ValOrFun.gettime[T](f288)
              (update[Stream2[T]](List(6118, f288), e92._1), BigInt(3) + e92._2)
            }
            (mc8._1, BigInt(7) + mc8._2)
        }
        val e104 = createQueuetime[T](e93._1, q.lenf77 - BigInt(1), ir59._1, q.r238, q.lenr77, ir59._2)
        (e104._1, ((BigInt(11) + e104._2) + e93._2) + ir9._2)
      case SNil1() =>
        val e105 = emptytime[T]
        (e105._1, BigInt(5) + e105._2)
    }
    (bd4._1, bd4._2)
  }
  
  def reversetime[T](q : Queue2[T]): (Queue2[T], BigInt) = (Queue2[T](q.r238, q.lenr77, q.sr75, q.f227, q.lenf77, q.sf75), BigInt(7))
  
  def snoc[T](x: T, q: Queue2[T]): Queue2[T] = {
    //require(q.valid)
    reversetime(constime(x, reversetime(q)._1)._1)._1
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    var size = points.map(x => BigInt(x)).toList

    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    points.foreach { length =>
      var rtd = emptytime[BigInt]()._1
      for (i <- 0 until length) {
        rtd = snoc[BigInt](BigInt(0), rtd)
      }
      ops :+= {() => reversetime[BigInt](rtd)._2}
      orb :+= {() => 7}
    }
    plot(size, ops, orb, "reverse", "orb")

    size = points.map(x => BigInt(x + 1)).toList

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { length =>
      var rtd = emptytime[BigInt]()._1
      for (i <- 0 until (length + 1)) {
        rtd = constime[BigInt](BigInt(0), rtd)._1
      }
      ops :+= {() => constime[BigInt](BigInt(0), rtd)._2}
      orb :+= {() => 528}
    }
    plot(size, ops, orb, "cons", "orb")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { length =>
      var rtd = emptytime[BigInt]()._1
      for (i <- 0 until (length + 1)) {
        rtd = constime[BigInt](BigInt(0), rtd)._1
      }
      rtd = reversetime[BigInt](rtd)._1
      ops :+= {() => tailtime[BigInt](rtd)._2}
      orb :+= {() => 1055}
    }
    plot(size, ops, orb, "tail", "orb")
  }

}

object ValOrFun {
  def gettime[T](thiss : RealTimeDeque.ValOrFun2[T]): (RealTimeDeque.Stream2[T], BigInt) = {
    val bd = thiss match {
      case RealTimeDeque.Fun3(f233) =>
        val e15 = f233()
        (e15._1, BigInt(4) + e15._2)
      case RealTimeDeque.Val1(x449) =>
        (x449, BigInt(4))
    }
    (bd._1, bd._2)
  }
}

object Queue {
  
}
