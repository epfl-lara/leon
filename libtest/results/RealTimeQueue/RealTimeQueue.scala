package RealTimeQueue

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
    var orb = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
      }
      ops :+= {() => dequeuetime[BigInt](rtq)._2}
      orb :+= {() => 71}
    }
    logplot(size, ops, orb, "dequeue")

    ops = List[() => BigInt]()
    orb = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
      }
      ops :+= {() => enqueuetime[BigInt](BigInt(0), rtq)._2}
      orb :+= {() => 39}
    }
    logplot(size, ops, orb, "enqueue")
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
