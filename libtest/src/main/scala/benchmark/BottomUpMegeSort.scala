package BottomUpMergeSort

import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.mem._
import leon.higherorder._
import leon.stats._

object BottomUpMergeSort {
  abstract class LList2
  
  case class SCons1(x321 : BigInt, tailFun1 : Stream2) extends LList2
  
  case class SNil1() extends LList2
  
  case class Stream2(lfun1 : () => (LList2, BigInt))
  
  @invisibleBody
  def pairstime(l : List[Stream2]): (List[Stream2], BigInt) = {
    val bd4 = l match {
      case Nil() =>
        (List[Stream2](), BigInt(3))
      case Cons(_, Nil()) =>
        (l, BigInt(5))
      case Cons(l118, Cons(l215, rest8)) =>
        val e34 = pairstime(rest8)
        (Cons[Stream2](Stream2(() => {
          val e30 = forceAndMergetime(l118, l215)
          (e30._1, BigInt(1) + e30._2)
        }), e34._1), BigInt(15) + e34._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def constructMergeTreetime(l : List[Stream2]): (List[Stream2], BigInt) = {
    val bd12 = l match {
      case Nil() =>
        (List[Stream2](), BigInt(3))
      case Cons(_, Nil()) =>
        (l, BigInt(5))
      case _ =>
        val e70 = pairstime(l)
        val e72 = constructMergeTreetime(e70._1)
        (e72._1, (BigInt(7) + e72._2) + e70._2)
    }
    (bd12._1, bd12._2)
  }
  
  @invisibleBody
  def mergetime(a : Stream2, b : Stream2): (LList2, BigInt) = {
    val lr2 = lookup[LList2](List(4959, b))
    val scr4 = if (lr2._1) {
      (lr2._2, BigInt(1))
    } else {
      val e40 = Stream.listtime(b)
      (update[LList2](List(4959, b), e40._1), BigInt(3) + e40._2)
    }
    val bd8 = scr4._1 match {
      case SNil1() =>
        val lr3 = lookup[LList2](List(4959, a))
        val mc7 = if (lr3._1) {
          (lr3._2, BigInt(1))
        } else {
          val e42 = Stream.listtime(a)
          (update[LList2](List(4959, a), e42._1), BigInt(3) + e42._2)
        }
        (mc7._1, (BigInt(2) + mc7._2) + scr4._2)
      case SCons1(x, xs34) =>
        val lr4 = lookup[LList2](List(4959, a))
        val scr5 = if (lr4._1) {
          (lr4._2, BigInt(1))
        } else {
          val e44 = Stream.listtime(a)
          (update[LList2](List(4959, a), e44._1), BigInt(3) + e44._2)
        }
        val mc10 = scr5._1 match {
          case SNil1() =>
            val lr5 = lookup[LList2](List(4959, b))
            val mc8 = if (lr5._1) {
              (lr5._2, BigInt(1))
            } else {
              val e46 = Stream.listtime(b)
              (update[LList2](List(4959, b), e46._1), BigInt(3) + e46._2)
            }
            (mc8._1, (BigInt(2) + mc8._2) + scr5._2)
          case SCons1(y, ys2) =>
            val mc9 = if (y < x) {
              (SCons1(y, Stream2(() => {
                val e50 = forceAndMergetime(ys2, b)
                (e50._1, BigInt(1) + e50._2)
              })), BigInt(5))
            } else {
              (SCons1(x, Stream2(() => {
                val e56 = forceAndMergetime(a, xs34)
                (e56._1, BigInt(1) + e56._2)
              })), BigInt(5))
            }
            (mc9._1, (BigInt(5) + mc9._2) + scr5._2)
        }
        (mc10._1, (BigInt(5) + mc10._2) + scr4._2)
    }
    (bd8._1, bd8._2)
  }
  
  @invisibleBody
  @usePost
  def forceAndMergetime(a : Stream2, b : Stream2): (LList2, BigInt) = {
    val lr = lookup[LList2](List(4959, a))
    val e16 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = Stream.listtime(a)
      (update[LList2](List(4959, a), e15._1), BigInt(3) + e15._2)
    }
    val lr1 = lookup[LList2](List(4959, b))
    val e19 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e18 = Stream.listtime(b)
      (update[LList2](List(4959, b), e18._1), BigInt(3) + e18._2)
    }
    val bd = {
      val _ = (e16._1, e19._1)
      val e22 = mergetime(a, b)
      (e22._1, ((BigInt(3) + e22._2) + e19._2) + e16._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def ListToStreamListtime(l : List[BigInt]): (List[Stream2], BigInt) = {
    val bd11 = l match {
      case Nil() =>
        (List[Stream2](), BigInt(3))
      case Cons(x, xs) =>
        val ir3 = SNil1()
        val ir4 = SCons1(x, Stream2(() => (ir3, BigInt(0))))
        val e67 = ListToStreamListtime(xs)
        (Cons[Stream2](Stream2(() => (ir4, BigInt(0))), e67._1), BigInt(15) + e67._2)
    }
    (bd11._1, bd11._2)
  }
  
  @invisibleBody
  def mergeSorttime(l : List[BigInt]): (Stream2, BigInt) = {
    val bd2 = l match {
      case Nil() =>
        val ir6 = SNil1()
        (Stream2(() => (ir6, BigInt(0))), BigInt(6))
      case _ =>
        val e25 = ListToStreamListtime(l)
        val e27 = constructMergeTreetime(e25._1)
        val mc3 = {
          val Cons(r160, Nil()) = e27._1
          (r160, (BigInt(7) + e27._2) + e25._2)
        }
        (mc3._1, BigInt(2) + mc3._2)
    }
    (bd2._1, bd2._2)
  }

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

object LList {
  
}

object Stream {
  def listtime(thiss : BottomUpMergeSort.Stream2): (BottomUpMergeSort.LList2, BigInt) = {
    val e38 = thiss.lfun1()
    (e38._1, BigInt(2) + e38._2)
  }
}
