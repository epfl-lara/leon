package Knapsack

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object Knapscak {
  abstract class IList
  
  case class Cons(x : (BigInt, BigInt), tail : IList) extends IList
  
  case class Nil() extends IList
  
  @invstate
  def maxValuetime(items : IList, w : BigInt, currList : IList): (BigInt, BigInt) = {
    val bd1 = currList match {
      case Cons((wi, vi), tail) =>
        val e36 = maxValuetime(items, w, tail)
        val e67 = e36._1
        val c13 = BigInt(3)
        val r160 = if (wi <= w && wi > BigInt(0)) {
          val e73 = w - wi
          val lr = lookup[BigInt](List(4861, e73, items))
          val e43 = if (lr._1) {
            (lr._2, BigInt(2))
          } else {
            val e42 = knapSacktime(e73, items)
            (update[BigInt](List(4861, e73, items), e42._1), BigInt(4) + e42._2)
          }
          val ir2 = (vi + e43._1, BigInt(1) + e43._2)
          val c10 = (ir2._1 >= e67, BigInt(1))
          val r159 = if (ir2._1 >= e67) {
            (ir2._1, BigInt(1) + c10._2)
          } else {
            (e67, BigInt(1) + c10._2)
          }
          (r159._1, ((BigInt(3) + c13) + r159._2) + e43._2)
        } else {
          (e67, BigInt(1) + c13)
        }
        (r160._1, (BigInt(9) + r160._2) + e36._2)
      case Nil() =>
        (BigInt(0), BigInt(5))
    }
    (bd1._1, bd1._2)
  }
  
  @memoize
  def knapSacktime(w : BigInt, items : IList): (BigInt, BigInt) = {
    val bd3 = if (w == BigInt(0)) {
      (BigInt(0), BigInt(2))
    } else {
      val e58 = maxValuetime(items, w, items)
      (e58._1, BigInt(3) + e58._2)
    }
    (bd3._1, bd3._2)
  }
  
  def invoketime(i : BigInt, items : IList): (BigInt, BigInt) = {
    val lr1 = lookup[BigInt](List(4861, i, items))
    val bd2 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e54 = knapSacktime(i, items)
      (update[BigInt](List(4861, i, items), e54._1), BigInt(3) + e54._2)
    }
    (bd2._1, bd2._2)
  }
  
  def bottomuptime(i : BigInt, w : BigInt, items : IList): (IList, BigInt) = {
    val e16 = invoketime(i, items)
    val e81 = e16._1
    val r158 = if (i == w) {
      (Cons((i, e81), Nil()), BigInt(5))
    } else {
      val e29 = bottomuptime(BigInt(1) + i, w, items)
      (Cons((i, e81), e29._1), BigInt(6) + e29._2)
    }
    (r158._1, (BigInt(2) + r158._2) + e16._2)
  }
  
  def knapSackSoltime(w : BigInt, items : IList): (IList, BigInt) = {
    val e64 = bottomuptime(BigInt(0), w, items)
    (e64._1, BigInt(1) + e64._2)
  }
  
}

object IList {
  
}
