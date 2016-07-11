package PreciseBottomUpMegeSort

import leon.collection._
import leon._
// import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.mem._
import leon.higherorder._
import leon.stats._
import leon.runtimeDriver._
import scala.math._


object BottomUpMergeSortPrecise {

  def mylog(x: BigInt) : BigInt = {
    if(x < 0) BigInt(1)
    else if(x == 0) BigInt(2)
    else
      1 + mylog(x/2)
  }

  
  abstract class LList2
  
  
  case class SCons1(x322 : BigInt, tailFun1 : Stream2) extends LList2
  
  
  case class SNil1() extends LList2
  
  
  case class Stream2(lfun1 : () => (LList2, BigInt))
  
  @invisibleBody
  def constructMergeTreetime(l : List[BigInt], from : BigInt, to : BigInt): ((LList2, List[BigInt]), BigInt) = {
    val bd2 = l match {
      case Nil() =>
        ((SNil1(), Nil[BigInt]()), BigInt(5))
      case Cons(x, tail) =>
        val mc5 = if (from == to) {
          ((SCons1(x, Stream2(() => (SNil1(), BigInt(1)))), tail), BigInt(6))
        } else {
          val ir7 = (from + to) / BigInt(2)
          val e37 = constructMergeTreetime(l, from, ir7)
          val ir1 = {
            val (lside, midlist) = e37._1
            ((lside, midlist), BigInt(6) + e37._2)
          }
          val ir9 = ir1._1
          val e47 = constructMergeTreetime(ir9._2, BigInt(1) + ir7, to)
          val ir4 = {
            val (rside, rest) = e47._1
            ((rside, rest), BigInt(7) + e47._2)
          }
          val ir15 = ir4._1
          val e54 = mergetime(ir9._1, ir15._1)
          ((e54._1, ir15._2), ((BigInt(10) + e54._2) + ir4._2) + ir1._2)
        }
        (mc5._1, BigInt(5) + mc5._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def mergetime(a : LList2, b : LList2): (LList2, BigInt) = {
    val bd5 = b match {
      case SNil1() =>
        (a, BigInt(2))
      case SCons1(x, xs34) =>
        val mc9 = a match {
          case SNil1() =>
            (b, BigInt(2))
          case SCons1(y, ys2) =>
            val mc8 = if (y < x) {
              (SCons1(y, Stream2(() => {
                val e62 = mergeSusptime(b, ys2)
                (e62._1, BigInt(1) + e62._2)
              })), BigInt(5))
            } else {
              (SCons1(x, Stream2(() => {
                val e68 = mergeSusptime(a, xs34)
                (e68._1, BigInt(1) + e68._2)
              })), BigInt(5))
            }
            (mc8._1, BigInt(5) + mc8._2)
        }
        (mc9._1, BigInt(5) + mc9._2)
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def mergeSusptime(a : LList2, b : Stream2): (LList2, BigInt) = {
    val lr = lookup[LList2](List(4963, b))
    val e79 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e78 = Stream.listtime(b)
      (update[LList2](List(4963, b), e78._1), BigInt(3) + e78._2)
    }
    val e80 = mergetime(a, e79._1)
    (e80._1, (BigInt(1) + e80._2) + e79._2)
  }
  
  @invisibleBody
  def mergeSorttime(l : List[BigInt]): (LList2, BigInt) = {
    val bd = l match {
      case Nil() =>
        (SNil1(), BigInt(3))
      case _ =>
        val e21 = constructMergeTreetime(l, BigInt(0), (l.size) - BigInt(1))
        (e21._1._1, BigInt(6) + e21._2)
    }
    (bd._1, bd._2)
  }
  
  def kthMinRectime(l : LList2, k : BigInt): (BigInt, BigInt) = {
    val bd9 = l match {
      case SCons1(x, xs35) =>
        val mc10 = if (k == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val lr1 = lookup[LList2](List(4963, xs35))
          val e88 = if (lr1._1) {
            (lr1._2, BigInt(1))
          } else {
            val e87 = Stream.listtime(xs35)
            (update[LList2](List(4963, xs35), e87._1), BigInt(3) + e87._2)
          }
          val e92 = kthMinRectime(e88._1, k - BigInt(1))
          (e92._1, (BigInt(4) + e92._2) + e88._2)
        }
        (mc10._1, BigInt(4) + mc10._2)
      case SNil1() =>
        (BigInt(0), BigInt(3))
    }
    (bd9._1, bd9._2)
  }
  
  def kthMintime(l : List[BigInt], k : BigInt): (BigInt, BigInt) = {
    val e82 = mergeSorttime(l)
    val e85 = kthMinRectime(e82._1, k)
    (e85._1, (BigInt(2) + e85._2) + e82._2)
  }
  
}

object LList {
  
}

object Stream {
  def listtime(thiss : BottomUpMergeSortPrecise.Stream2): (BottomUpMergeSortPrecise.LList2, BigInt) = {
    val e75 = thiss.lfun1()
    (e75._1, BigInt(2) + e75._2)
  }
}
