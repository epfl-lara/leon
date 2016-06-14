package WeightedScheduling

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object WeightedSched {
  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  @extern
  def jobInfotime(i : BigInt): ((BigInt, BigInt, BigInt), BigInt) = (((0, 0, 0), 1) : ((BigInt, BigInt, BigInt), BigInt))
  
  @extern
  def prevCompatibleJobtime(i : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  @invisibleBody
  @invstate
  @memoize
  def schedtime(jobIndex : BigInt): (BigInt, BigInt) = {
    val e31 = jobInfotime(jobIndex)
    val ir1 = {
      val (st, fn, w) = e31._1
      ((st, fn, w), BigInt(6) + e31._2)
    }
    val ir18 = ir1._1._3
    val r162 = if (jobIndex == BigInt(0)) {
      (ir18, BigInt(2))
    } else {
      val e54 = jobIndex - BigInt(1)
      val lr1 = lookup[BigInt](List(4872, e54))
      val ir5 = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e41 = schedtime(e54)
        (update[BigInt](List(4872, e54), e41._1), BigInt(4) + e41._2)
      }
      val e43 = prevCompatibleJobtime(jobIndex)
      val e59 = e43._2
      val e58 = e43._1
      val lr2 = lookup[BigInt](List(4872, e58))
      val ir6 = if (lr2._1) {
        (lr2._2, BigInt(1) + e59)
      } else {
        val e45 = schedtime(e58)
        (update[BigInt](List(4872, e58), e45._1), (BigInt(3) + e45._2) + e59)
      }
      val ir7 = (ir18 + ir6._1, BigInt(1))
      val c10 = (ir7._1 >= ir5._1, BigInt(1))
      val r159 = if (ir7._1 >= ir5._1) {
        (ir7._1, BigInt(1) + c10._2)
      } else {
        (ir5._1, BigInt(1) + c10._2)
      }
      (r159._1, ((BigInt(3) + r159._2) + ir6._2) + ir5._2)
    }
    (r162._1, (BigInt(3) + r162._2) + ir1._2)
  }
  
  @invisibleBody
  def invoketime(jobIndex : BigInt): (BigInt, BigInt) = {
    val lr = lookup[BigInt](List(4872, jobIndex))
    val bd = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = schedtime(jobIndex)
      (update[BigInt](List(4872, jobIndex), e15._1), BigInt(3) + e15._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def schedBUtime(jobi : BigInt): (IList, BigInt) = {
    val bd1 = if (jobi == BigInt(0)) {
      val e17 = invoketime(jobi)
      (Cons(e17._1, Nil()), BigInt(5) + e17._2)
    } else {
      val e23 = schedBUtime(jobi - BigInt(1))
      val e25 = invoketime(jobi)
      (Cons(e25._1, e23._1), (BigInt(6) + e25._2) + e23._2)
    }
    (bd1._1, bd1._2)
  }
  
}

object IList {
  
}
