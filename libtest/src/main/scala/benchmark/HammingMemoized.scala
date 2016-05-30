package HammingMemoized

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object Hamming {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  case class Data(v : BigInt, i2 : BigInt, i3 : BigInt, i5 : BigInt)
  
  @invstate
  @memoize
  def hamtime(n : BigInt): (Data, BigInt) = {
    val bd1 = if (n == BigInt(0)) {
      (Data(BigInt(1), BigInt(0), BigInt(0), BigInt(0)), BigInt(3))
    } else {
      val e179 = n - BigInt(1)
      val lr1 = lookup[Data](List(4865, e179))
      val scr = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e24 = hamtime(e179)
        (update[Data](List(4865, e179), e24._1), BigInt(4) + e24._2)
      }
      val ir = {
        val Data(x, i2, i3, i5) = scr._1
        ((x, i2, i3, i5), BigInt(7) + scr._2)
      }
      val ir2 = (ir._1._2, BigInt(1))
      val e31 = (ir._1, BigInt(0))
      val ir3 = (ir._1._3, BigInt(1) + e31._2)
      val ir4 = (ir._1._4, BigInt(1))
      val e33 = (ir2._1, BigInt(0))
      val lr2 = lookup[Data](List(4865, ir2._1))
      val e35 = if (lr2._1) {
        (lr2._2, BigInt(1) + e33._2)
      } else {
        val e34 = hamtime(ir2._1)
        (update[Data](List(4865, ir2._1), e34._1), (BigInt(3) + e34._2) + e33._2)
      }
      val e36 = (e35._1.v, BigInt(1) + e35._2)
      val ir5 = (e35._1.v * BigInt(2), BigInt(1) + e36._2)
      val e38 = (ir3._1, BigInt(0))
      val lr3 = lookup[Data](List(4865, ir3._1))
      val e40 = if (lr3._1) {
        (lr3._2, BigInt(1) + e38._2)
      } else {
        val e39 = hamtime(ir3._1)
        (update[Data](List(4865, ir3._1), e39._1), (BigInt(3) + e39._2) + e38._2)
      }
      val ir6 = (e40._1.v * BigInt(3), BigInt(2) + e40._2)
      val e43 = (ir4._1, BigInt(0))
      val lr4 = lookup[Data](List(4865, ir4._1))
      val e45 = if (lr4._1) {
        (lr4._2, BigInt(1) + e43._2)
      } else {
        val e44 = hamtime(ir4._1)
        (update[Data](List(4865, ir4._1), e44._1), (BigInt(3) + e44._2) + e43._2)
      }
      val e46 = (e45._1.v, BigInt(1) + e45._2)
      val ir7 = (e45._1.v * BigInt(5), BigInt(1) + e46._2)
      val e130 = (ir5._1, BigInt(0))
      val e131 = (ir6._1, BigInt(0))
      val e132 = (ir5._1 == ir6._1, (BigInt(1) + e131._2) + e130._2)
      val e133 = (ir6._1, BigInt(0))
      val e134 = (ir7._1, BigInt(0))
      val e135 = (ir6._1 == ir7._1, (BigInt(1) + e134._2) + e133._2)
      val c11 = (e132._1 && e135._1, (((BigInt(3) + e134._2) + e133._2) + e131._2) + e130._2)
      val scr1 = if (e132._1 && e135._1) {
        ((ir5._1, BigInt(1) + ir2._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1), BigInt(5) + c11._2)
      } else {
        val e124 = (ir5._1, BigInt(0))
        val e125 = (ir6._1, BigInt(0))
        val e126 = (ir5._1 == ir6._1, (BigInt(1) + e125._2) + e124._2)
        val e127 = (ir5._1, BigInt(0))
        val e128 = (ir7._1, BigInt(0))
        val e129 = (ir5._1 < ir7._1, (BigInt(1) + e128._2) + e127._2)
        val c12 = (e126._1 && e129._1, (((BigInt(3) + e128._2) + e127._2) + e125._2) + e124._2)
        val el5 = if (e126._1 && e129._1) {
          ((ir5._1, BigInt(1) + ir2._1, BigInt(1) + ir3._1, ir4._1), BigInt(4) + c12._2)
        } else {
          val e118 = (ir5._1, BigInt(0))
          val e119 = (ir7._1, BigInt(0))
          val e120 = (ir5._1 == ir7._1, (BigInt(1) + e119._2) + e118._2)
          val e121 = (ir5._1, BigInt(0))
          val e122 = (ir6._1, BigInt(0))
          val e123 = (ir5._1 < ir6._1, (BigInt(1) + e122._2) + e121._2)
          val c13 = (e120._1 && e123._1, (((BigInt(3) + e122._2) + e121._2) + e119._2) + e118._2)
          val el4 = if (e120._1 && e123._1) {
            ((ir5._1, BigInt(1) + ir2._1, ir3._1, BigInt(1) + ir4._1), BigInt(4) + c13._2)
          } else {
            val e112 = (ir6._1, BigInt(0))
            val e113 = (ir7._1, BigInt(0))
            val e114 = (ir6._1 == ir7._1, (BigInt(1) + e113._2) + e112._2)
            val e115 = (ir6._1, BigInt(0))
            val e116 = (ir5._1, BigInt(0))
            val e117 = (ir6._1 < ir5._1, (BigInt(1) + e116._2) + e115._2)
            val c14 = (e114._1 && e117._1, (((BigInt(3) + e116._2) + e115._2) + e113._2) + e112._2)
            val el3 = if (e114._1 && e117._1) {
              ((ir6._1, ir2._1, BigInt(1) + ir3._1, BigInt(1) + ir4._1), BigInt(4) + c14._2)
            } else {
              val e106 = (ir5._1, BigInt(0))
              val e107 = (ir6._1, BigInt(0))
              val e108 = (ir5._1 < ir6._1, (BigInt(1) + e107._2) + e106._2)
              val e109 = (ir5._1, BigInt(0))
              val e110 = (ir7._1, BigInt(0))
              val e111 = (ir5._1 < ir7._1, (BigInt(1) + e110._2) + e109._2)
              val c15 = (e108._1 && e111._1, (((BigInt(3) + e110._2) + e109._2) + e107._2) + e106._2)
              val el2 = if (e108._1 && e111._1) {
                ((ir5._1, BigInt(1) + ir2._1, ir3._1, ir4._1), BigInt(3) + c15._2)
              } else {
                val e100 = (ir6._1, BigInt(0))
                val e101 = (ir7._1, BigInt(0))
                val e102 = (ir6._1 < ir7._1, (BigInt(1) + e101._2) + e100._2)
                val e103 = (ir6._1, BigInt(0))
                val e104 = (ir5._1, BigInt(0))
                val e105 = (ir6._1 < ir5._1, (BigInt(1) + e104._2) + e103._2)
                val c16 = (e102._1 && e105._1, (((BigInt(3) + e104._2) + e103._2) + e101._2) + e100._2)
                val el1 = if (e102._1 && e105._1) {
                  ((ir6._1, ir2._1, BigInt(1) + ir3._1, ir4._1), BigInt(3) + c16._2)
                } else {
                  ((ir7._1, ir2._1, ir3._1, BigInt(1) + ir4._1), BigInt(3) + c16._2)
                }
                (el1._1, (BigInt(1) + c15._2) + el1._2)
              }
              (el2._1, (BigInt(1) + c14._2) + el2._2)
            }
            (el3._1, (BigInt(1) + c13._2) + el3._2)
          }
          (el4._1, (BigInt(1) + c12._2) + el4._2)
        }
        (el5._1, (BigInt(1) + c11._2) + el5._2)
      }
      val ir8 = {
        val (v, ni, nj, nk) = scr1._1
        ((v, ni, nj, nk), BigInt(7) + scr1._2)
      }
      (Data(ir8._1._1, ir8._1._2, ir8._1._3, ir8._1._4), (((((BigInt(28) + ir8._2) + e46._2) + e40._2) + e36._2) + e31._2) + ir._2)
    }
    (bd1._1, bd1._2)
  }
  
  def invoketime(n : BigInt): (BigInt, BigInt) = {
    val lr = lookup[Data](List(4865, n))
    val e16 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = hamtime(n)
      (update[Data](List(4865, n), e15._1), BigInt(3) + e15._2)
    }
    (e16._1.v, BigInt(1) + e16._2)
  }
  
  def hammingListtime(n : BigInt): (IList, BigInt) = {
    val bd2 = if (n == BigInt(0)) {
      val e151 = invoketime(n)
      (Cons(e151._1, Nil()), BigInt(5) + e151._2)
    } else {
      val e157 = hammingListtime(n - BigInt(1))
      val e159 = invoketime(n)
      (Cons(e159._1, e157._1), (BigInt(7) + e159._2) + e157._2)
    }
    (bd2._1, bd2._2)
  }
  
}
