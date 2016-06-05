package RealTimeQueuewithrun

import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.invariant._

object RealTimeQueue0 {
  abstract class Stream0[T]

  case class CSons[T](x0 : T, tailFun18 : tStreamT00[T]) extends Stream0[T]
  
  case class NSil0[T]() extends Stream0[T]
  
  case class Queue0[T](f10 : Stream0[T], r1 : List[T], s4 : Stream0[T])


  def tailmemtime0[T](that: Stream0[T], st46 : Set[MemoFuns0[T]]): ((Stream0[T], Set[MemoFuns0[T]]), BigInt) = {
    val bd4 = {
      val CSons(x165, tailFun35) = that
      val e138 = evaltStreamT0time0[T](tailFun35, st46)
      (e138._1, BigInt(5) + e138._2)
    }
    (bd4._1, bd4._2)
  }

  @invisibleBody
  @invstate
  def rotatetime0[T](f169 : Stream0[T], r212 : List[T], a201 : Stream0[T], st40 : Set[MemoFuns0[T]]): ((Stream0[T], Set[MemoFuns0[T]]), BigInt) = {
    val bd0 = (f169, r212) match {
      case (NSil0(), Cons(y6, _)) =>
        ((CSons[T](y6, AnonFun1L0[T](a201)), st40), BigInt(10))
      case (c4 @ CSons(x20, _), Cons(y7, r10)) =>
        val e23 = tailmemtime0(c4, st40)
        val e195 = e23._1
        ((CSons[T](x20, RotateL0[T](e195._1, r10, CSons[T](y7, AnonFun1L0[T](a201)))), e195._2 ++ Set[MemoFuns0[T]](TailMem0[T](c4))), BigInt(21) + (if (st40.contains(TailMem0[T](c4))) {
          BigInt(1)
        } else {
          BigInt(2) + e23._2
        }))
    }
    (bd0._1, bd0._2)
  }
  
  def enqueuetime0[T](x346 : T, q6 : Queue0[T], st43 : Set[MemoFuns0[T]]): ((Queue0[T], Set[MemoFuns0[T]]), BigInt) = {
    val ir42 = q6.f10
    val ir44 = Cons[T](x346, q6.r1)
    val r241 = q6.s4 match {
      case c16 @ CSons(_, _) =>
        val e51 = tailmemtime0(c16, st43)
        val e243 = e51._1
        ((Queue0[T](ir42, ir44, e243._1), e243._2 ++ Set[MemoFuns0[T]](TailMem0[T](c16))), BigInt(5) + (if (st43.contains(TailMem0[T](c16))) {
          BigInt(1)
        } else {
          BigInt(2) + e51._2
        }))
      case NSil0() =>
        val e67 = rotatetime0[T](ir42, ir44, NSil0[T](), st43)
        val e258 = e67._1
        val ir52 = e258._1
        ((Queue0[T](ir52, Nil[T](), ir52), e258._2), BigInt(9) + e67._2)
    }
    (r241._1, BigInt(5) + r241._2)
  }
  
  def dequeuetime0[T](q9 : Queue0[T], st44 : Set[MemoFuns0[T]]): ((Queue0[T], Set[MemoFuns0[T]]), BigInt) = {
    val bd2 = {
      val c8 @ CSons(x26, _) = q9.f10
      val e79 = tailmemtime0(c8, st44)
      val e139 = e79._1
      val ir22 = e139._1
      val e149 = e139._2 ++ Set[MemoFuns0[T]](TailMem0[T](c8))
      val ir16 = q9.r1
      val r254 = q9.s4 match {
        case c17 @ CSons(_, _) =>
          val e93 = tailmemtime0(c17, e149)
          val e153 = e93._1
          ((Queue0[T](ir22, ir16, e153._1), e153._2 ++ Set[MemoFuns0[T]](TailMem0[T](c17))), BigInt(5) + (if (e149.contains(TailMem0[T](c17))) {
            BigInt(1)
          } else {
            BigInt(2) + e93._2
          }))
        case NSil0() =>
          val e112 = rotatetime0[T](ir22, ir16, NSil0[T](), e149)
          val e174 = e112._1
          val ir28 = e174._1
          ((Queue0[T](ir28, Nil[T](), ir28), e174._2), BigInt(9) + e112._2)
      }
      (r254._1, (BigInt(8) + r254._2) + (if (st44.contains(TailMem0[T](c8))) {
        BigInt(1)
      } else {
        BigInt(2) + e79._2
      }))
    }
    (bd2._1, bd2._2)
  }
  
  abstract class tStreamT00[T]
  
  case class AnonFun1L0[T](a188 : Stream0[T]) extends tStreamT00[T]
  
  case class RotateL0[T](ftail1 : Stream0[T], r11 : List[T], newa1 : Stream0[T]) extends tStreamT00[T]
  
  abstract class MemoFuns0[T]
  
  case class TailMem0[T](thiss699 : Stream0[T]) extends MemoFuns0[T]
  
  @axiom
  def evaltStreamT0time0[T](cl2 : tStreamT00[T], st2 : Set[MemoFuns0[T]]): ((Stream0[T], Set[MemoFuns0[T]]), BigInt) = {
    val bd3 = cl2 match {
      case t372 : AnonFun1L0[T] =>
        ((t372.a188, st2), BigInt(0))
      case t373 : RotateL0[T] =>
        val e131 = rotatetime0[T](t373.ftail1, t373.r11, t373.newa1, st2)
        val e233 = e131._1
        ((e233._1, e233._2), e131._2)
    }
    (bd3._1, bd3._2)
  }
}
