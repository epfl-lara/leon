package BottomUpMegeSort

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.mem._
import leon.higherorder._
import leon.stats._
import leon.runtimeDriver._

object BottomUpMergeSort {
  
  abstract class LList2
  
  
  case class SCons1(x322 : BigInt, tailFun1 : Stream2) extends LList2
  
  
  case class SNil1() extends LList2
  
  
  case class Stream2(lfun1 : () => (LList2, BigInt))
  
  @invisibleBody
  def pairstime(l : List[Stream2]): (List[Stream2], BigInt) = {
    val bd5 = l match {
      case Nil() =>
        (List[Stream2](), BigInt(3))
      case Cons(_, Nil()) =>
        (l, BigInt(5))
      case Cons(l118, Cons(l215, rest8)) =>
        val e43 = pairstime(rest8)
        (Cons[Stream2](Stream2(() => {
          val e39 = forceAndMergetime(l118, l215)
          (e39._1, BigInt(1) + e39._2)
        }), e43._1), BigInt(15) + e43._2)
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def constructMergeTreetime(l : List[Stream2]): (List[Stream2], BigInt) = {
    val bd13 = l match {
      case Nil() =>
        (List[Stream2](), BigInt(3))
      case Cons(_, Nil()) =>
        (l, BigInt(5))
      case _ =>
        val e79 = pairstime(l)
        val e81 = constructMergeTreetime(e79._1)
        (e81._1, (BigInt(7) + e81._2) + e79._2)
    }
    (bd13._1, bd13._2)
  }
  
  def mergetime(a : Stream2, b : Stream2): (LList2, BigInt) = {
    val lr3 = lookup[LList2](List(4972, b))
    val scr5 = if (lr3._1) {
      (lr3._2, BigInt(1))
    } else {
      val e46 = Stream.listtime(b)
      (update[LList2](List(4972, b), e46._1), BigInt(3) + e46._2)
    }
    val bd8 = scr5._1 match {
      case SNil1() =>
        val lr4 = lookup[LList2](List(4972, a))
        val mc9 = if (lr4._1) {
          (lr4._2, BigInt(1))
        } else {
          val e48 = Stream.listtime(a)
          (update[LList2](List(4972, a), e48._1), BigInt(3) + e48._2)
        }
        (mc9._1, (BigInt(2) + mc9._2) + scr5._2)
      case SCons1(x, xs36) =>
        val lr5 = lookup[LList2](List(4972, a))
        val scr6 = if (lr5._1) {
          (lr5._2, BigInt(1))
        } else {
          val e50 = Stream.listtime(a)
          (update[LList2](List(4972, a), e50._1), BigInt(3) + e50._2)
        }
        val mc12 = scr6._1 match {
          case SNil1() =>
            val lr6 = lookup[LList2](List(4972, b))
            val mc10 = if (lr6._1) {
              (lr6._2, BigInt(1))
            } else {
              val e52 = Stream.listtime(b)
              (update[LList2](List(4972, b), e52._1), BigInt(3) + e52._2)
            }
            (mc10._1, (BigInt(2) + mc10._2) + scr6._2)
          case SCons1(y, ys2) =>
            val mc11 = if (y < x) {
              (SCons1(y, Stream2(() => {
                val e56 = forceAndMergetime(ys2, b)
                (e56._1, BigInt(1) + e56._2)
              })), BigInt(5))
            } else {
              (SCons1(x, Stream2(() => {
                val e62 = forceAndMergetime(a, xs36)
                (e62._1, BigInt(1) + e62._2)
              })), BigInt(5))
            }
            (mc11._1, (BigInt(5) + mc11._2) + scr6._2)
        }
        (mc12._1, (BigInt(5) + mc12._2) + scr5._2)
    }
    (bd8._1, bd8._2)
  }
  
  @invisibleBody
  @usePost
  def forceAndMergetime(a : Stream2, b : Stream2): (LList2, BigInt) = {
    val lr = lookup[LList2](List(4972, a))
    val e16 = if (lr._1) {
      (lr._2, BigInt(1))
    } else {
      val e15 = Stream.listtime(a)
      (update[LList2](List(4972, a), e15._1), BigInt(3) + e15._2)
    }
    val lr1 = lookup[LList2](List(4972, b))
    val e19 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e18 = Stream.listtime(b)
      (update[LList2](List(4972, b), e18._1), BigInt(3) + e18._2)
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
        val e73 = ListToStreamListtime(xs)
        (Cons[Stream2](Stream2(() => (ir4, BigInt(0))), e73._1), BigInt(15) + e73._2)
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
  
  def kthMintime(s : Stream2, k : BigInt): (BigInt, BigInt) = {
    val lr2 = lookup[LList2](List(4972, s))
    val scr3 = if (lr2._1) {
      (lr2._2, BigInt(1))
    } else {
      val e29 = Stream.listtime(s)
      (update[LList2](List(4972, s), e29._1), BigInt(3) + e29._2)
    }
    val bd3 = scr3._1 match {
      case SCons1(x, xs35) =>
        val mc4 = if (k == BigInt(0)) {
          (x, BigInt(2))
        } else {
          val e34 = kthMintime(xs35, k - BigInt(1))
          (e34._1, BigInt(4) + e34._2)
        }
        (mc4._1, (BigInt(4) + mc4._2) + scr3._2)
      case SNil1() =>
        (BigInt(0), BigInt(3) + scr3._2)
    }
    (bd3._1, bd3._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).toList
    
    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      ops :+= {() => ListToStreamListtime(input)._2}
      orb :+= {() => 13 * i + 3}
    }
    run(size, ops, orb, "ListToStreamList")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      // NOTE: floor take for coeff
      ops :+= {() => constructMergeTreetime(ListToStreamListtime(input)._1)._2}
      orb :+= {() => 34* i + 3}
    }
    run(size, ops, orb, "constructMergeTree")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      val s = mergeSorttime(input)._1
      // NOTE: floor take for coeff
      ops :+= {() => kthMintime(s, 10)._2}
      orb :+= {() => 123 * (10 * i) + 123 * i + 9}
    }
    run(size, ops, orb, "kthMin")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    points.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      ops :+= {() => mergeSorttime(input)._2}
      orb :+= {() => 47 * i + 15}
    }
    run(size, ops, orb, "mergeSort")

    val newpoints = points.map(x => (x/2)).toList
    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    newpoints.foreach { i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(n, f)  
        }
      }
      val s = mergeSorttime(input)._1
      ops :+= {() => forceAndMergetime(s, s)._2}
      orb :+= {() => 123 * 2 * i - 86 }
    }
    run(size, ops, orb, "forceAndMerge")
  }
  
}

object LList {
  
}

object Stream {
  def listtime(thiss : BottomUpMergeSort.Stream2): (BottomUpMergeSort.LList2, BigInt) = {
    val e77 = thiss.lfun1()
    (e77._1, BigInt(2) + e77._2)
  }
}
