package FibonacciMemoizedwithinst

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._

object FibMem0 {
  ////////////////////////////////////////////
  abstract class IList0
  
  case class Cons0(x0 : BigInt, tail0 : IList0) extends IList0
  
  case class Nil0() extends IList0
  
  def fibRecmemtime0(n6 : BigInt): (BigInt, BigInt) = {
    val bd0 = if (n6 <= BigInt(2)) {
      (BigInt(1), BigInt(2))
    } else {
      val e48 = n6 - BigInt(1)
      var opers = BigInt(0)
      var temp = (BigInt(0), BigInt(0))
      var res = BigInt(0)
      if(lookup[BigInt](List(1896, e48))._1) {
        val e20 = lookup[BigInt](List(1896, e48))._2
        res = res + e20
        opers = opers + BigInt(1)
      } else {
        temp = fibRecmemtime0(e48)
        val e20 = temp._1
        res = res + e20
        opers = opers + BigInt(3) + temp._2
        update[BigInt](List(1896, e48), e20)
      }
      val e52 = n6 - BigInt(2)
      if(lookup[BigInt](List(1896, e52))._1) {
        val e32 = lookup[BigInt](List(1896, e52))._2
        res = res + e32
        opers = opers + BigInt(1)
      } else {
        temp = fibRecmemtime0(e52)
        val e32 = temp._1
        res = res + e32
        opers = opers + BigInt(4) + temp._2
        update[BigInt](List(1896, e52), e32)
      }
      (res, opers)
    }
    (bd0._1, bd0._2)
  }
  
  abstract class MemoFuns0
  
  case class FibRecMem(n5 : BigInt) extends MemoFuns0
  ////////////////////////////////////////

  abstract class IList
  
  case class Cons(x : BigInt, tail : IList) extends IList
  
  case class Nil() extends IList
  
  @memoize
  def fibRectime(n : BigInt): (BigInt, BigInt) = {
    val bd = if (n <= BigInt(2)) {
      (BigInt(1), BigInt(2))
    } else {
      val e26 = n - BigInt(1)
      val lr = lookup[BigInt](List(4814, e26))
      val e18 = if (lr._1) {
        (lr._2, BigInt(2))
      } else {
        val e17 = fibRectime(e26)
        (update[BigInt](List(4814, e26), e17._1), BigInt(4) + e17._2)
      }
      val e30 = n - BigInt(2)
      val lr1 = lookup[BigInt](List(4814, e30))
      val e23 = if (lr1._1) {
        (lr1._2, BigInt(2))
      } else {
        val e22 = fibRectime(e30)
        (update[BigInt](List(4814, e30), e22._1), BigInt(4) + e22._2)
      }
      (e18._1 + e23._1, (BigInt(3) + e23._2) + e18._2)
    }
    (bd._1, bd._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000) // can change this
    val size = points.map(x => BigInt(x)).toList
    
    var ops = List[() => BigInt]()
    var inst = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {() => {
          leon.mem.clearMemo()
          fibRectime(input)._2
        }
      }
      inst :+= {() => 
          leon.mem.clearMemo()
          fibRecmemtime0(input)._2
      }
    }
    plot(size, ops, inst, "fibmem", "inst")
  }  
}
