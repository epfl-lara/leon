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
  
  def fibRecmemtime0(n6 : BigInt, st1 : Set[MemoFuns0]): ((BigInt, Set[MemoFuns0]), BigInt) = {
    val bd0 = if (n6 <= BigInt(2)) {
      ((BigInt(1), st1), BigInt(2))
    } else {
      val e48 = n6 - BigInt(1)
      val e20 = fibRecmemtime0(e48, st1)
      val e50 = e20._1
      val e52 = n6 - BigInt(2)
      val e62 = e50._2 ++ Set[MemoFuns0](FibRecMem(n6 - BigInt(1)))
      val e32 = fibRecmemtime0(e52, e62)
      val e64 = e32._1
      ((e50._1 + e64._1, e64._2 ++ Set[MemoFuns0](FibRecMem(n6 - BigInt(2)))), (BigInt(6) + (if (e62.contains(FibRecMem(e52))) {
        BigInt(1)
      } else {
        BigInt(4) + e32._2
      })) + (if (st1.contains(FibRecMem(e48))) {
        BigInt(1)
      } else {
        BigInt(3) + e20._2
      }))
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

    val points = (10 to 200 by 10) // can change this
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
          fibRecmemtime0(input, Set[MemoFuns0]())._2
      }
    }
    plot(size, ops, inst, "fibmem", "inst")
  }  
}
