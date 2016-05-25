package RealTimeDeque

import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.math._
import leon.invariant._

object RealTimeDeque {  
  abstract class Stream2[T]
  
  case class SCons1[T](x442 : T, next64 : ValOrFun2[T]) extends Stream2[T]
  
  case class SNil1[T]() extends Stream2[T]
  
  abstract class ValOrFun2[T]
  
  case class Val1[T](x440 : Stream2[T]) extends ValOrFun2[T]
  
  case class Fun3[T](fun23 : () => (Stream2[T], BigInt)) extends ValOrFun2[T]
  
  case class Queue2[T](f226 : Stream2[T], lenf77 : BigInt, sf75 : Stream2[T], r238 : Stream2[T], lenr77 : BigInt, sr75 : Stream2[T])
  
  @invstate
  def takeLazytime[T](n : BigInt, l : Stream2[T]): (Stream2[T], BigInt) = {
    val bd14 = {
      val c45 @ SCons1(x, _) = l
      val mc28 = if (n == BigInt(1)) {
        (SCons1[T](x, Val1[T](SNil1[T]())), BigInt(5))
      } else {
        val ir53 = n - BigInt(1)
        val ir21 = c45 match {
          case SCons1(_, Val1(x611)) =>
            (x611, BigInt(5))
          case SCons1(_, f347 @ Fun3(_)) =>
            val lr6 = lookup[Stream2[T]](List(6113, f347))
            val mc27 = if (lr6._1) {
              (lr6._2, BigInt(1))
            } else {
              val e222 = ValOrFun.gettime[T](f347)
              (update[Stream2[T]](List(6113, f347), e222._1), BigInt(3) + e222._2)
            }
            (mc27._1, BigInt(7) + mc27._2)
        }
        (SCons1[T](x, Fun3[T](() => {
          val e226 = takeLazytime[T](ir53, ir21._1)
          (e226._1, BigInt(1) + e226._2)
        })), BigInt(8) + ir21._2)
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
          case SCons1(_, Val1(x562)) =>
            (x562, BigInt(5))
          case SCons1(_, f339 @ Fun3(_)) =>
            val lr4 = lookup[Stream2[T]](List(6113, f339))
            val mc20 = if (lr4._1) {
              (lr4._2, BigInt(1))
            } else {
              val e188 = ValOrFun.gettime[T](f339)
              (update[Stream2[T]](List(6113, f339), e188._1), BigInt(3) + e188._2)
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
            case SCons1(_, Val1(x555)) =>
              (x555, BigInt(5))
            case SCons1(_, f337 @ Fun3(_)) =>
              val lr3 = lookup[Stream2[T]](List(6113, f337))
              val mc16 = if (lr3._1) {
                (lr3._2, BigInt(1))
              } else {
                val e182 = ValOrFun.gettime[T](f337)
                (update[Stream2[T]](List(6113, f337), e182._1), BigInt(3) + e182._2)
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
            case SCons1(_, Val1(x619)) =>
              (x619, BigInt(5))
            case SCons1(_, f349 @ Fun3(_)) =>
              val lr7 = lookup[Stream2[T]](List(6113, f349))
              val mc31 = if (lr7._1) {
                (lr7._2, BigInt(1))
              } else {
                val e236 = ValOrFun.gettime[T](f349)
                (update[Stream2[T]](List(6113, f349), e236._1), BigInt(3) + e236._2)
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
          case SCons1(_, Val1(x579)) =>
            (x579, BigInt(5))
          case SCons1(_, f342 @ Fun3(_)) =>
            val lr5 = lookup[Stream2[T]](List(6113, f342))
            val mc24 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e199 = ValOrFun.gettime[T](f342)
              (update[Stream2[T]](List(6113, f342), e199._1), BigInt(3) + e199._2)
            }
            (mc24._1, BigInt(7) + mc24._2)
        }
        val e202 = droptime[T](BigInt(2), f)
        val e330 = e202._1
        val e205 = taketime[T](BigInt(2), f)
        val e208 = revAppendtime[T](e205._1, a)
        val e336 = e208._1
        (SCons1[T](x, Fun3[T](() => {
          val e213 = rotateRevtime[T](ir17._1, e330, e336)
          (e213._1, BigInt(1) + e213._2)
        })), (((BigInt(13) + e208._2) + e205._2) + e202._2) + ir17._2)
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
          case SCons1(_, Val1(x522)) =>
            (x522, BigInt(5))
          case SCons1(_, f305 @ Fun3(_)) =>
            val lr2 = lookup[Stream2[T]](List(6113, f305))
            val mc12 = if (lr2._1) {
              (lr2._2, BigInt(1))
            } else {
              val e114 = ValOrFun.gettime[T](f305)
              (update[Stream2[T]](List(6113, f305), e114._1), BigInt(3) + e114._2)
            }
            (mc12._1, BigInt(7) + mc12._2)
        }
        val ir24 = i - BigInt(2)
        val e119 = droptime[T](BigInt(2), f)
        val e302 = e119._1
        (SCons1[T](x, Fun3[T](() => {
          val e124 = rotateDroptime[T](ir12._1, ir24, e302)
          (e124._1, BigInt(1) + e124._2)
        })), (BigInt(11) + e119._2) + ir12._2)
      }
      (el2._1, (BigInt(1) + c56) + el2._2)
    }
    (bd6._1, bd6._2)
  }
  
  @invisibleBody
  def createQueuetime[T](f : Stream2[T], lenf : BigInt, sf : Stream2[T], r : Stream2[T], lenr : BigInt, sr : Stream2[T]): (Queue2[T], BigInt) = {
    val c58 = BigInt(3)
    val bd2 = if (lenf > BigInt(1) + BigInt(2) * lenr) {
      val ir32 = (lenf + lenr) / BigInt(2)
      val e33 = rotateDroptime[T](r, ir32, f)
      val e358 = e33._1
      val e36 = takeLazytime[T](ir32, f)
      val e360 = e36._1
      (Queue2[T](e360, ir32, e360, e358, (lenf + lenr) - ir32, e358), ((BigInt(12) + c58) + e36._2) + e33._2)
    } else {
      val c60 = BigInt(3)
      val el1 = if (lenr > BigInt(1) + BigInt(2) * lenf) {
        val ir40 = (lenf + lenr) / BigInt(2)
        val ir42 = (lenf + lenr) - ir40
        val e54 = rotateDroptime[T](f, ir42, r)
        val e370 = e54._1
        val e57 = takeLazytime[T](ir42, r)
        val e372 = e57._1
        (Queue2[T](e370, ir40, e370, e372, ir42, e372), ((BigInt(12) + c60) + e57._2) + e54._2)
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
            val lr = lookup[Stream2[T]](List(6113, f237))
            val mc1 = if (lr._1) {
              (lr._2, BigInt(1))
            } else {
              val e15 = ValOrFun.gettime[T](f237)
              (update[Stream2[T]](List(6113, f237), e15._1), BigInt(3) + e15._2)
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
    val e262 = forcetime[T](q.sf75, q.f226, q.r238, q.sr75)
    val e270 = forcetime[T](e262._1, q.f226, q.r238, q.sr75)
    val e435 = e270._1
    val e278 = forcetime[T](q.sr75, q.r238, q.f226, e435)
    val e285 = forcetime[T](e278._1, q.r238, q.f226, e435)
    ((e435, e285._1), (((BigInt(19) + e285._2) + e278._2) + e270._2) + e262._2)
  }
  
  def emptytime[T](): (Queue2[T], BigInt) = {
    val ir48 = SNil1[T]()
    (Queue2[T](ir48, BigInt(0), ir48, ir48, BigInt(0), ir48), BigInt(3))
  }
  
  def constime[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val e141 = forcetime[T](q.sf75, q.f226, q.r238, q.sr75)
    val e382 = e141._1
    val e149 = forcetime[T](q.sr75, q.r238, q.f226, e382)
    val e165 = createQueuetime[T](SCons1[T](x, Val1[T](q.f226)), BigInt(1) + q.lenf77, e382, q.r238, q.lenr77, e149._1)
    (e165._1, ((BigInt(19) + e165._2) + e149._2) + e141._2)
  }
  
  def tailtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val e251 = forcetime[T](q.f226, q.sf75, q.r238, q.sr75)
    val bd16 = {
      val _ = e251._1
      val e253 = tailSubtime[T](q)
      (e253._1, (BigInt(7) + e253._2) + e251._2)
    }
    (bd16._1, bd16._2)
  }
  
  def tailSubtime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd3 = q.f226 match {
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
            val lr1 = lookup[Stream2[T]](List(6113, f268))
            val mc6 = if (lr1._1) {
              (lr1._2, BigInt(1))
            } else {
              val e90 = ValOrFun.gettime[T](f268)
              (update[Stream2[T]](List(6113, f268), e90._1), BigInt(3) + e90._2)
            }
            (mc6._1, BigInt(7) + mc6._2)
        }
        val e102 = createQueuetime[T](e91._1, q.lenf77 - BigInt(1), ir59._1, q.r238, q.lenr77, ir59._2)
        (e102._1, ((BigInt(14) + e102._2) + e91._2) + ir9._2)
      case SNil1() =>
        val e103 = emptytime[T]
        (e103._1, BigInt(5) + e103._2)
    }
    (bd3._1, bd3._2)
  }
  
  def reversetime[T](q : Queue2[T]): (Queue2[T], BigInt) = (Queue2[T](q.r238, q.lenr77, q.sr75, q.f226, q.lenf77, q.sf75), BigInt(7))

  def main(args: Array[String]): Unit = {
    // import scala.util.Random
    // val rand = Random

    // val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    // val size = points.map(x => BigInt(2*x)).toList
    
    // var ops = List[() => BigInt]()
    // var orb = List[() => BigInt]()
    // points.foreach { i =>
    //   val input = {
    //     (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
    //       Cons(n, f)  
    //     }
    //   }
    //   ops :+= {() => sorttime(input)._2}
    //   orb :+= {() => 15 * i + 10}
    // }
    // run(size, ops, orb, "sort")

    // ops = List[() => BigInt]()
    // orb = List[() => BigInt]()
    // points.foreach { i =>
    //   val input = {
    //     (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
    //       Cons(n, f)  
    //     }
    //   }
    //   // NOTE: floor take for coeff
    //   ops :+= {() => kthMintime(Stream2(()=>sorttime(input)), 10)._2}
    //   orb :+= {() => 15 * 10 * i + 33 * 10 + 0}
    // }
    // run(size, ops, orb, "kthMintime")
  }
}

object Stream {
  
}

object ValOrFun {
  def gettime[T](thiss : RealTimeDeque.ValOrFun2[T]): (RealTimeDeque.Stream2[T], BigInt) = {
    val bd4 = thiss match {
      case RealTimeDeque.Fun3(f280) =>
        val e105 = f280()
        (e105._1, BigInt(4) + e105._2)
      case RealTimeDeque.Val1(x503) =>
        (x503, BigInt(4))
    }
    (bd4._1, bd4._2)
  }
}

object Queue {
  
}
