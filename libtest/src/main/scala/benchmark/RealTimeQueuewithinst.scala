package RealTimeQueuewithinst

import leon.collection._
import leon._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._

object RealTimeQueue {
  
  ///////////////////////////////////////////////////////////
  abstract class Stream0[T]

  case class CSons[T](x0 : T, tailFun18 : tStreamT00[T]) extends Stream0[T]
  
  case class NSil0[T]() extends Stream0[T]

  case class Queue0[T](f10 : Stream0[T], r1 : List[T], s4 : Stream0[T])

  def empty0[T] = {
    val a: Stream0[T] = NSil0[T]()
    Queue0(a, Nil[T](), a)
  }
  
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
  ///////////////////////////////////////////////////////

  abstract class Stream2[T]
  
  
  case class SCons1[T](x345 : T, tailFun19 : () => (Stream2[T], BigInt)) extends Stream2[T]
  
  
  case class SNil1[T]() extends Stream2[T]
  
  
  case class Queue2[T](f159 : Stream2[T], r196 : List[T], s106 : Stream2[T])


  def empty[T] = {
    val a: Stream2[T] = SNil1[T]()
    Queue2(a, Nil[T](), a)
  }
  
  @invisibleBody
  @invstate
  def rotatetime[T](f : Stream2[T], r : List[T], a : Stream2[T]): (Stream2[T], BigInt) = {
    val bd4 = (f, r) match {
      case (SNil1(), Cons(y, _)) =>
        (SCons1[T](y, () => (a, BigInt(0))), BigInt(10))
      case (c19 @ SCons1(x, _), Cons(y, r1)) =>
        val ir9 = SCons1[T](y, () => (a, BigInt(0)))
        val lr = lookup[Stream2[T]](List(5264, c19))
        val ir1 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e23 = Stream.tailtime[T](c19)
          (update[Stream2[T]](List(5264, c19), e23._1), BigInt(3) + e23._2)
        }
        (SCons1[T](x, () => {
          val e27 = rotatetime[T](ir1._1, r1, ir9)
          (e27._1, BigInt(1) + e27._2)
        }), BigInt(22) + ir1._2)
    }
    (bd4._1, bd4._2)
  }
  
  def enqueuetime[T](x : T, q : Queue2[T]): (Queue2[T], BigInt) = {
    val ir11 = q.f159
    val ir13 = Cons[T](x, q.r196)
    val r214 = q.s106 match {
      case c20 @ SCons1(_, _) =>
        val lr1 = lookup[Stream2[T]](List(5264, c20))
        val e39 = if (lr1._1) {
          (lr1._2, BigInt(1))
        } else {
          val e38 = Stream.tailtime[T](c20)
          (update[Stream2[T]](List(5264, c20), e38._1), BigInt(3) + e38._2)
        }
        (Queue2[T](ir11, ir13, e39._1), BigInt(4) + e39._2)
      case SNil1() =>
        val e43 = rotatetime[T](ir11, ir13, SNil1[T]())
        val e75 = e43._1
        (Queue2[T](e75, List[T](), e75), BigInt(9) + e43._2)
    }
    (r214._1, BigInt(5) + r214._2)
  }
  
  def dequeuetime[T](q : Queue2[T]): (Queue2[T], BigInt) = {
    val bd6 = {
      val c23 @ SCons1(x, _) = q.f159
      val lr2 = lookup[Stream2[T]](List(5264, c23))
      val ir6 = if (lr2._1) {
        (lr2._2, BigInt(1))
      } else {
        val e49 = Stream.tailtime[T](c23)
        (update[Stream2[T]](List(5264, c23), e49._1), BigInt(3) + e49._2)
      }
      val ir17 = q.r196
      val r227 = q.s106 match {
        case c24 @ SCons1(_, _) =>
          val lr3 = lookup[Stream2[T]](List(5264, c24))
          val e56 = if (lr3._1) {
            (lr3._2, BigInt(1))
          } else {
            val e55 = Stream.tailtime[T](c24)
            (update[Stream2[T]](List(5264, c24), e55._1), BigInt(3) + e55._2)
          }
          (Queue2[T](ir6._1, ir17, e56._1), BigInt(4) + e56._2)
        case SNil1() =>
          val e60 = rotatetime[T](ir6._1, ir17, SNil1[T]())
          (Queue2[T](e60._1, List[T](), e60._1), BigInt(9) + e60._2)
      }
      (r227._1, (BigInt(7) + r227._2) + ir6._2)
    }
    (bd6._1, bd6._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (3 to 18)
    val size = points.map(x => ((1 << x) - 2)).toList
    val size2 = points.map(x => BigInt((1 << x) - 2)).toList

    var ops = List[() => BigInt]()
    var inst = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      var instrtq = empty0[BigInt]
      var set = Set[MemoFuns0[BigInt]]()
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
        val s = enqueuetime0[BigInt](BigInt(0), instrtq, set)._1
        instrtq = s._1
        set = s._2
      }
      ops :+= {() => dequeuetime[BigInt](rtq)._2}
      inst :+= {() => dequeuetime0[BigInt](instrtq, set)._2}
    }
    logplot(size, ops, inst, "dequeue", "inst")

    ops = List[() => BigInt]()
    inst = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      var instrtq = empty0[BigInt]
      var set = Set[MemoFuns0[BigInt]]()
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
        val s = enqueuetime0[BigInt](BigInt(0), instrtq, set)._1
        instrtq = s._1
        set = s._2
      }
      ops :+= {() => enqueuetime[BigInt](BigInt(0), rtq)._2}
      inst :+= {() => enqueuetime0[BigInt](BigInt(0), instrtq, set)._2}
    }
    logplot(size, ops, inst, "enqueue", "inst")
  }
  
}

object Stream {
  def tailtime[T](thiss : RealTimeQueue.Stream2[T]): (RealTimeQueue.Stream2[T], BigInt) = {
    val bd = {
      val RealTimeQueue.SCons1(x, tailFun21) = thiss
      val e15 = tailFun21()
      (e15._1, BigInt(5) + e15._2)
    }
    (bd._1, bd._2)
  }
}

object Queue {
  
}
