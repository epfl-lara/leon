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
  
  
  case class Queue2[T](f228 : Stream2[T], lenf77 : BigInt, sf75 : Stream2[T], r238 : Stream2[T], lenr77 : BigInt, sr75 : Stream2[T])
  
  @invstate
  def takeLazytime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd13 = {
      val c45 @ SCons1(x, _) = l
      val mc26 = if (n == BigInt(1)) {
        (SCons1[T](x, Val1[T](SNil1[T]())), BigInt(5))
      } else {
        val ir53 = n - BigInt(1)
        val ir21 = c45 match {
          case SCons1(_, Val1(x609)) =>
            (x609, BigInt(5))
          case SCons1(_, f348 @ Fun3(_)) =>
            val lr6 = lookup[Stream2[T]](List(6122, f348))
            val mc25 = if (lr6._1) {
              (lr6._2, BigInt(1))
            } else {
              val e220 = ValOrFun.gettime[T](f348)
              (update[Stream2[T]](List(6122, f348), e220._1), BigInt(3) + e220._2)
            }
            (mc25._1, BigInt(7) + mc25._2)
        }
        (SCons1[T](x, Fun3[T](() => {
          val e224 = takeLazytime[T](ir53, ir21._1)
          (e224._1, BigInt(1) + e224._2)
        })), BigInt(6) + ir21._2)
      }
      (mc26._1, BigInt(3) + mc26._2)
    }
    (bd13._1, bd13._2)
  }
  
  @invstate
  def revAppendtime[T](l1 : Stream2[T], l2 : Stream2[T]): (Stream2[T], BigInt) = {
    val bd9 = l1 match {
      case SNil1() =>
        (l2, BigInt(2))
      case c39 @ SCons1(x, _) =>
        val e187 = c39 match {
          case SCons1(_, Val1(x560)) =>
            (x560, BigInt(5))
          case SCons1(_, f338 @ Fun3(_)) =>
            val lr4 = lookup[Stream2[T]](List(6122, f338))
            val mc18 = if (lr4._1) {
              (lr4._2, BigInt(1))
            } else {
              val e186 = ValOrFun.gettime[T](f338)
              (update[Stream2[T]](List(6122, f338), e186._1), BigInt(3) + e186._2)
            }
            (mc18._1, BigInt(7) + mc18._2)
        }
        val e192 = revAppendtime[T](e187._1, SCons1[T](x, Val1[T](l2)))
        (e192._1, (BigInt(7) + e192._2) + e187._2)
    }
    (bd9._1, bd9._2)
  }
  
  @invstate
  def droptime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd8 = if (n == BigInt(0)) {
      (l, BigInt(2))
    } else {
      val el3 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c38 @ SCons1(x, _) =>
          val e181 = c38 match {
            case SCons1(_, Val1(x553)) =>
              (x553, BigInt(5))
            case SCons1(_, f336 @ Fun3(_)) =>
              val lr3 = lookup[Stream2[T]](List(6122, f336))
              val mc14 = if (lr3._1) {
                (lr3._2, BigInt(1))
              } else {
                val e180 = ValOrFun.gettime[T](f336)
                (update[Stream2[T]](List(6122, f336), e180._1), BigInt(3) + e180._2)
              }
              (mc14._1, BigInt(7) + mc14._2)
          }
          val e182 = droptime[T](n - BigInt(1), e181._1)
          (e182._1, (BigInt(6) + e182._2) + e181._2)
      }
      (el3._1, BigInt(2) + el3._2)
    }
    (bd8._1, bd8._2)
  }
  
  @invstate
  def taketime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd14 = if (n == BigInt(0)) {
      (SNil1[T](), BigInt(3))
    } else {
      val el5 = l match {
        case SNil1() =>
          (l, BigInt(2))
        case c48 @ SCons1(x, _) =>
          val e235 = c48 match {
            case SCons1(_, Val1(x617)) =>
              (x617, BigInt(5))
            case SCons1(_, f350 @ Fun3(_)) =>
              val lr7 = lookup[Stream2[T]](List(6122, f350))
              val mc29 = if (lr7._1) {
                (lr7._2, BigInt(1))
              } else {
                val e234 = ValOrFun.gettime[T](f350)
                (update[Stream2[T]](List(6122, f350), e234._1), BigInt(3) + e234._2)
              }
              (mc29._1, BigInt(7) + mc29._2)
          }
          val e236 = taketime[T](n - BigInt(1), e235._1)
          (SCons1[T](x, Val1[T](e236._1)), (BigInt(8) + e236._2) + e235._2)
      }
      (el5._1, BigInt(2) + el5._2)
    }
    (bd14._1, bd14._2)
  }
  
  @invstate
  def rotateRevtime[T](r : Stream2[T], f : Stream2[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd11 = r match {
      case SNil1() =>
        val e195 = revAppendtime[T](f, a)
        (e195._1, BigInt(3) + e195._2)
      case c41 @ SCons1(x, _) =>
        val ir17 = c41 match {
          case SCons1(_, Val1(x577)) =>
            (x577, BigInt(5))
          case SCons1(_, f341 @ Fun3(_)) =>
            val lr5 = lookup[Stream2[T]](List(6122, f341))
            val mc22 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e197 = ValOrFun.gettime[T](f341)
              (update[Stream2[T]](List(6122, f341), e197._1), BigInt(3) + e197._2)
            }
            (mc22._1, BigInt(7) + mc22._2)
        }
        val e200 = droptime[T](BigInt(2), f)
        val e348 = e200._1
        val e203 = taketime[T](BigInt(2), f)
        val e206 = revAppendtime[T](e203._1, a)
        val e354 = e206._1
        (SCons1[T](x, Fun3[T](() => {
          val e211 = rotateRevtime[T](ir17._1, e348, e354)
          (e211._1, BigInt(1) + e211._2)
        })), (((BigInt(10) + e206._2) + e203._2) + e200._2) + ir17._2)
    }
    (bd11._1, bd11._2)
  }
  
  @invstate
  def rotateDroptime[T](r : Stream2[T], i : BigInt, f : Stream2[T]): (Stream2[T], BigInt) = {
    val c62 = BigInt(4)
    val bd5 = if (i < BigInt(2) || r == SNil1[T]()) {
      val e107 = droptime[T](i, f)
      val e110 = rotateRevtime[T](r, e107._1, SNil1[T]())
      (e110._1, ((BigInt(4) + c62) + e110._2) + e107._2)
    } else {
      val el2 = {
        val c32 @ SCons1(x, _) = r
        val ir12 = c32 match {
          case SCons1(_, Val1(x520)) =>
            (x520, BigInt(5))
          case SCons1(_, f286 @ Fun3(_)) =>
            val lr2 = lookup[Stream2[T]](List(6122, f286))
            val mc10 = if (lr2._1) {
              (lr2._2, BigInt(1))
            } else {
              val e112 = ValOrFun.gettime[T](f286)
              (update[Stream2[T]](List(6122, f286), e112._1), BigInt(3) + e112._2)
            }
            (mc10._1, BigInt(7) + mc10._2)
        }
        val ir49 = i - BigInt(2)
        val e117 = droptime[T](BigInt(2), f)
        val e406 = e117._1
        (SCons1[T](x, Fun3[T](() => {
          val e122 = rotateDroptime[T](ir12._1, ir49, e406)
          (e122._1, BigInt(1) + e122._2)
        })), (BigInt(8) + e117._2) + ir12._2)
      }
      (el2._1, (BigInt(1) + c62) + el2._2)
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def createQueuetime[T](f : Stream2[T], lenf : BigInt, sf : Stream2[T], r : Stream2[T], lenr : BigInt, sr : Stream2[T]): (Queue2[T], BigInt) = {
    val c58 = BigInt(3)
    val bd2 = if (lenf > BigInt(1) + BigInt(2) * lenr) {
      val ir24 = (lenf + lenr) / BigInt(2)
      val e33 = rotateDroptime[T](r, ir24, f)
      val e316 = e33._1
      val e36 = takeLazytime[T](ir24, f)
      val e318 = e36._1
      (Queue2[T](e318, ir24, e318, e316, (lenf + lenr) - ir24, e316), ((BigInt(8) + c58) + e36._2) + e33._2)
    } else {
      val c60 = BigInt(3)
      val el1 = if (lenr > BigInt(1) + BigInt(2) * lenf) {
        val ir32 = (lenf + lenr) / BigInt(2)
        val ir34 = (lenf + lenr) - ir32
        val e54 = rotateDroptime[T](f, ir34, r)
        val e328 = e54._1
        val e57 = takeLazytime[T](ir34, r)
        val e330 = e57._1
        (Queue2[T](e328, ir32, e328, e330, ir34, e330), ((BigInt(8) + c60) + e57._2) + e54._2)
      } else {
        (Queue2[T](f, lenf, sf, r, lenr, sr), BigInt(2) + c60)
      }
      (el1._1, (BigInt(1) + c58) + el1._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def forcetime[T](tar : Stream2[T], htar : Stream2[T], other : Stream2[T], hother : Stream2[T]): (Stream2[T], BigInt) = {
    val bd = tar match {
      case c21 @ SCons1(_, _) =>
        val mc2 = c21 match {
          case SCons1(_, Val1(x458)) =>
            (x458, BigInt(5))
          case SCons1(_, f237 @ Fun3(_)) =>
            val lr = lookup[Stream2[T]](List(6122, f237))
            val mc1 = if (lr._1) {
              (lr._2, BigInt(1))
            } else {
              val e15 = ValOrFun.gettime[T](f237)
              (update[Stream2[T]](List(6122, f237), e15._1), BigInt(3) + e15._2)
            }
            (mc1._1, BigInt(7) + mc1._2)
        }
        (mc2._1, BigInt(2) + mc2._2)
      case _ =>
        (tar, BigInt(2))
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def forceTwicetime[T](q : Queue2[T]): ((Stream2[T], Stream2[T]), BigInt) = {
    val e260 = forcetime[T](q.sf75, q.f228, q.r238, q.sr75)
    val e268 = forcetime[T](e260._1, q.f228, q.r238, q.sr75)
    val e374 = e268._1
    val e276 = forcetime[T](q.sr75, q.r238, q.f228, e374)
    val e283 = forcetime[T](e276._1, q.r238, q.f228, e374)
    ((e374, e283._1), (((BigInt(17) + e283._2) + e276._2) + e268._2) + e260._2)
  }
  
  def emptytime[T](): (Queue2[T], BigInt) = {
    val ir40 = SNil1[T]()
    (Queue2[T](ir40, BigInt(0), ir40, ir40, BigInt(0), ir40), BigInt(2))
  }
  
  def constime[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val e139 = forcetime[T](q.sf75, q.f228, q.r238, q.sr75)
    val e425 = e139._1
    val e147 = forcetime[T](q.sr75, q.r238, q.f228, e425)
    val e163 = createQueuetime[T](SCons1[T](x, Val1[T](q.f228)), BigInt(1) + q.lenf77, e425, q.r238, q.lenr77, e147._1)
    (e163._1, ((BigInt(17) + e163._2) + e147._2) + e139._2)
  }
  
  def tailtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val e249 = forcetime[T](q.f228, q.sf75, q.r238, q.sr75)
    val bd15 = {
      val _ = e249._1
      val e251 = tailSubtime[T](q)
      (e251._1, (BigInt(7) + e251._2) + e249._2)
    }
    (bd15._1, bd15._2)
  }
  
  def tailSubtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd3 = q.f228 match {
      case c28 @ SCons1(x, _) =>
        val e84 = forceTwicetime[T](q)
        val ir9 = {
          val (nsf, nsr) = e84._1
          ((nsf, nsr), BigInt(6) + e84._2)
        }
        val ir59 = ir9._1
        val e91 = c28 match {
          case SCons1(_, Val1(x498)) =>
            (x498, BigInt(5))
          case SCons1(_, f268 @ Fun3(_)) =>
            val lr1 = lookup[Stream2[T]](List(6122, f268))
            val mc6 = if (lr1._1) {
              (lr1._2, BigInt(1))
            } else {
              val e90 = ValOrFun.gettime[T](f268)
              (update[Stream2[T]](List(6122, f268), e90._1), BigInt(3) + e90._2)
            }
            (mc6._1, BigInt(7) + mc6._2)
        }
        val e102 = createQueuetime[T](e91._1, q.lenf77 - BigInt(1), ir59._1, q.r238, q.lenr77, ir59._2)
        (e102._1, ((BigInt(11) + e102._2) + e91._2) + ir9._2)
      case SNil1() =>
        val e103 = emptytime[T]
        (e103._1, BigInt(5) + e103._2)
    }
    (bd3._1, bd3._2)
  }
  
  def reversetime[T](q : Queue2[T]): (Queue2[T], BigInt) = (Queue2[T](q.r238, q.lenr77, q.sr75, q.f228, q.lenf77, q.sf75), BigInt(7))
  
}

object Stream {
  
}

object ValOrFun {
  def gettime[T](thiss : RealTimeDeque.ValOrFun2[T]): (RealTimeDeque.Stream2[T], BigInt) = {
    val bd17 = thiss match {
      case RealTimeDeque.Fun3(f381) =>
        val e287 = f381()
        (e287._1, BigInt(4) + e287._2)
      case RealTimeDeque.Val1(x660) =>
        (x660, BigInt(4))
    }
    (bd17._1, bd17._2)
  }
}

object Queue {
  
}
