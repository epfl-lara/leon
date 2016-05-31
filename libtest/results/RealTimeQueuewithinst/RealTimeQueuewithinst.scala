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
  abstract class Stream0[T0]

  def tailmemtime0[T364](thiss727 : Stream0[T364]): (Stream0[T364], BigInt) = {
    val bd0 = {
      val CSons0(x165, tailFun35) = thiss727
      val e16 = evaltStreamT0time0[T364](tailFun35)
      (e16._1, BigInt(5) + e16._2)
    }
    (bd0._1, bd0._2)
  }
  
  case class CSons0[T0](x0 : T0, tailFun18 : tStreamT00[T0]) extends Stream0[T0]
  
  case class NSil0[T0]() extends Stream0[T0]
  
  case class Queue0[T8](f10 : Stream0[T8], r1 : List[T8], s4 : Stream0[T8])
  
  def empty0[T] = {
    val a: Stream0[T] = NSil0()
    Queue0(a, Nil(), a)
  }

  @invisibleBody
  @invstate
  def rotatetime0[T4](f169 : Stream0[T4], r212 : List[T4], a206 : Stream0[T4]): (Stream0[T4], BigInt) = {
    val bd2 = (f169, r212) match {
      case (NSil0(), Cons(y6, _)) =>
        (CSons0[T4](y6, AnonFun1L0[T4](a206)), BigInt(10))
      case (c4 @ CSons0(x20, _), Cons(y7, r10)) =>
      	var e71:(Stream0[T4], BigInt) = null
      	var opers: BigInt = 0
      	if(lookup[(Stream0[T4], BigInt)](List(1896, c4))._1) {
        	e71 = lookup[(Stream0[T4], BigInt)](List(1896, c4))._2
        	opers = opers + 1
        } else {
        	e71 = tailmemtime0(c4)
        	update[(Stream0[T4], BigInt)](List(1896, c4), e71)
        	opers = opers + 3 + e71._2
        }
        (CSons0[T4](x20, RotateL0[T4](e71._1, r10, CSons0[T4](y7, AnonFun1L0[T4](a206)))), BigInt(19) + opers)
    }
    (bd2._1, bd2._2)
  }
  
  def enqueuetime0[T12](x346 : T12, q6 : Queue0[T12]): (Queue0[T12], BigInt) = {
    val ir16 = q6.f10
    val ir18 = Cons[T12](x346, q6.r1)
    val r266 = q6.s4 match {
      case c16 @ CSons0(_, _) =>

      	var e114:(Stream0[T12], BigInt) = null
      	var opers: BigInt = 0
      	if(lookup[(Stream0[T12], BigInt)](List(1896, c16))._1) {
        	e114 = lookup[(Stream0[T12], BigInt)](List(1896, c16))._2
        	opers = opers + 1
        } else {
        	e114 = tailmemtime0(c16)
        	update[(Stream0[T12], BigInt)](List(1896, c16), e114)
        	opers = opers + 3 + e114._2
        }
        (Queue0[T12](ir16, ir18, e114._1), BigInt(4) + opers)

      case NSil0() =>
        val e130 = rotatetime0[T12](ir16, ir18, NSil0[T12]())
        val e172 = e130._1
        (Queue0[T12](e172, Nil[T12](), e172), BigInt(8) + e130._2)
    }
    (r266._1, BigInt(3) + r266._2)
  }
  
  def dequeuetime0[T13](q9 : Queue0[T13]): (Queue0[T13], BigInt) = {
    val bd1 = {
      val c8 @ CSons0(x26, _) = q9.f10


      var e20:(Stream0[T13], BigInt) = null
      var oopers: BigInt = 0
      if(lookup[(Stream0[T13], BigInt)](List(1896, c8))._1) {
       	e20 = lookup[(Stream0[T13], BigInt)](List(1896, c8))._2
       	oopers = oopers + 1
      } else {
       	e20 = tailmemtime0(c8)
       	update[(Stream0[T13], BigInt)](List(1896, c8), e20)
       	oopers = oopers + 3 + e20._2
      }
      // val e20 = tailmemtime0(c8)

      val e191 = e20._1
      val ir38 = e191

      val ir32 = q9.r1
      val r245 = q9.s4 match {
        case c17 @ CSons0(_, _) =>

	        var e34:(Stream0[T13], BigInt) = null
	      	var iopers: BigInt = 0
	      	if(lookup[(Stream0[T13], BigInt)](List(1896, c17))._1) {
	        	e34 = lookup[(Stream0[T13], BigInt)](List(1896, c17))._2
	        	iopers = iopers + 1
	        } else {
	        	e34 = tailmemtime0(c17)
	        	update[(Stream0[T13], BigInt)](List(1896, c17), e34)
	        	iopers = iopers + 3 + e34._2
	        }

          // val e34 = tailmemtime0(c17)
          val e205 = e34._1
          (Queue0[T13](ir38, ir32, e205), BigInt(4) + iopers)

        case NSil0() =>
          val e53 = rotatetime0[T13](ir38, ir32, NSil0[T13]())
          val e226 = e53._1
          val ir44 = e226
          (Queue0[T13](ir44, Nil[T13](), ir44), BigInt(8) + e53._2)
      }

      (r245._1, (BigInt(5) + r245._2) + oopers)
    }
    (bd1._1, bd1._2)
  }
  
  abstract class tStreamT00[T11]
  
  case class AnonFun1L0[T4](a188 : Stream0[T4]) extends tStreamT00[T4]
  
  case class RotateL0[T4](ftail1 : Stream0[T4], r11 : List[T4], newa1 : Stream0[T4]) extends tStreamT00[T4]
  
  abstract class MemoFuns0[T10]
  
  case class TailmemM0[T364](thiss699 : Stream0[T364]) extends MemoFuns0[T364]
  
  @axiom
  def evaltStreamT0time0[T4](cl2 : tStreamT00[T4]): (Stream0[T4], BigInt) = {
    val bd3 = cl2 match {
      case t372 : AnonFun1L0[T4] =>
        (t372.a188, BigInt(0))
      case t373 : RotateL0[T4] =>
        val e102 = rotatetime0[T4](t373.ftail1, t373.r11, t373.newa1)
        val e147 = e102._1
        (e147, e102._2)
    }
    (bd3._1, bd3._2)
  }
  ///////////////////////////////////////////////////////

  abstract class Stream2[T]
  
  
  case class SCons1[T](x345 : T, tailFun19 : () => (Stream2[T], BigInt)) extends Stream2[T]
  
  
  case class SNil1[T]() extends Stream2[T]
  
  
  case class Queue2[T](f159 : Stream2[T], r196 : List[T], s106 : Stream2[T])
  
  def empty[T] = {
    val a: Stream2[T] = SNil1()
    Queue2(a, Nil(), a)
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
        }), BigInt(19) + ir1._2)
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
        (Queue2[T](e75, List[T](), e75), BigInt(8) + e43._2)
    }
    (r214._1, BigInt(3) + r214._2)
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
          (Queue2[T](e60._1, List[T](), e60._1), BigInt(8) + e60._2)
      }
      (r227._1, (BigInt(5) + r227._2) + ir6._2)
    }
    (bd6._1, bd6._2)
  }
  
  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (3 to 13)
    val size = points.map(x => ((1 << x) - 2)).toList
    val size2 = points.map(x => BigInt((1 << x) - 2)).toList

    var ops = List[() => BigInt]()
    var inst = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      var instrtq = empty0[BigInt]
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
        instrtq = enqueuetime0[BigInt](BigInt(0), instrtq)._1
      }
      ops :+= {() => dequeuetime[BigInt](rtq)._2}
      inst :+= {() => dequeuetime0[BigInt](instrtq)._2}
    }
    // dumplogdata(size, ops, inst, "dequeue", "inst")
    logplot(size, ops, inst, "dequeue", "inst")

    ops = List[() => BigInt]()
    inst = List[() => BigInt]()
    size.foreach { length =>
      var rtq = empty[BigInt]
      var instrtq = empty0[BigInt]
      for (i <- 0 until length) {
        rtq = enqueuetime[BigInt](BigInt(0), rtq)._1
        instrtq = enqueuetime0[BigInt](BigInt(0), instrtq)._1
      }
      ops :+= {() => enqueuetime[BigInt](BigInt(0), rtq)._2}
      inst :+= {() => enqueuetime0[BigInt](BigInt(0), instrtq)._2}
    }
    // dumplogdata(size, ops, inst, "enqueue", "inst")
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
