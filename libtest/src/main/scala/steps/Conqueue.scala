package Conqueue

import leon.collection._
import leon._
import leon.collection._
import leon.mem._
import leon.higherorder._
import leon.lang._
import leon.math._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import ConcTrees.ConcTrees._

object Conqueue {
  
  abstract class ConList2[T]
  
  
  case class Tip1[T](t405 : Conc[T]) extends ConList2[T]
  
  
  case class Spine1[T](head58 : Conc[T], rear65 : Stream2[T]) extends ConList2[T]
  
  
  abstract class Stream2[T]
  
  
  case class Val1[T](x372 : ConList2[T]) extends Stream2[T]
  
  
  case class Susp1[T](fun13 : () => (ConList2[T], BigInt)) extends Stream2[T]
  
  
  case class Conqueue3[T](trees11 : Stream2[T], schedule11 : List[Stream2[T]])
  
  @invisibleBody
  def pushLeftStreamtime[T](ys : Single[T], xs : Stream2[T]): (ConList2[T], BigInt) = {
    val e103 = Stream.gettime[T](xs)
    val scr43 = BigInt(1) + e103._2
    val bd2 = e103._1 match {
      case Tip1(CC[T]) =>
        (Spine1[T](ys, xs), BigInt(5) + scr43)
      case Tip1(Empty()) =>
        (Tip1[T](ys), BigInt(8) + scr43)
      case Tip1(t @ Single(_)) =>
        (Tip1[T](CC[T](ys, t)), BigInt(12) + scr43)
      case s77 @ Spine1(Empty(), rear81) =>
        (Spine1[T](ys, rear81), BigInt(15) + scr43)
      case s78 @ Spine1(_, _) =>
        val e114 = pushLeftLazytime[T](ys, xs)
        (e114._1, (BigInt(15) + e114._2) + scr43)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  @invstate
  def pushLeftLazytime[T](ys : Conc[T], xs : Stream2[T]): (ConList2[T], BigInt) = {
    val e121 = Stream.gettime[T](xs)
    val bd5 = {
      val Spine1(head, rear102) = e121._1
      val ir16 = CC[T](head, ys)
      val e125 = Stream.gettime[T](rear102)
      val scr29 = BigInt(1) + e125._2
      val r204 = e125._1 match {
        case Tip1(tree) =>
          val c26 = BigInt(3)
          val mc13 = if ((tree.level  ) > (ir16.level )) {
            (Spine1[T](Empty[T](), Val1[T](Spine1[T](ir16, rear102))), BigInt(5) + c26)
          } else {
            (Spine1[T](Empty[T](), Val1[T](Spine1[T](Empty[T](), Val1[T](Tip1[T](CC[T](tree, ir16)))))), BigInt(9) + c26)
          }
          (mc13._1, (BigInt(3) + mc13._2) + scr29)
        case Spine1(Empty(), srearfun2) =>
          (Spine1[T](Empty[T](), Val1[T](Spine1[T](ir16, srearfun2))), BigInt(10) + scr29)
        case s80 =>
          (Spine1[T](Empty[T](), Susp1[T](() => {
            val e154 = pushLeftLazytime[T](ir16, rear102)
            (e154._1, BigInt(1) + e154._2)
          })), BigInt(9) + scr29)
      }
      (r204._1, (BigInt(6) + r204._2) + e121._2)
    }
    (bd5._1, bd5._2)
  }
  
  @invisibleBody
  def pushLefttime[T](ys : Single[T], w : Conqueue3[T]): ((Stream2[T], List[Stream2[T]]), BigInt) = {
    val e166 = pushLeftStreamtime[T](ys, w.trees11)
    val e402 = e166._1
    val ir9 = e402 match {
      case Spine1(Empty(), rear136 : Susp1[T]) =>
        (Cons[Stream2[T]](rear136, w.schedule11), BigInt(8))
      case _ =>
        (w.schedule11, BigInt(7))
    }
    ((Val1[T](e402), ir9._1), (BigInt(4) + ir9._2) + e166._2)
  }
  
  @invisibleBody
  def Paytime[T](q : Stream2[T], scheds : List[Stream2[T]]): (List[Stream2[T]], BigInt) = {
    val bd7 = scheds match {
      case c17 @ Cons(head102, rest13) =>
        val e160 = Stream.gettime[T](head102)
        val scr21 = BigInt(1) + e160._2
        val mc21 = e160._1 match {
          case Spine1(Empty(), rear119 : Susp1[T]) =>
            (Cons[Stream2[T]](rear119, rest13), BigInt(7) + scr21)
          case _ =>
            (rest13, BigInt(6) + scr21)
        }
        (mc21._1, BigInt(4) + mc21._2)
      case Nil() =>
        (scheds, BigInt(3))
    }
    (bd7._1, bd7._2)
  }
  
  @invisibleBody
  def pushLeftAndPaytime[T](ys : Single[T], w : Conqueue3[T]): (Conqueue3[T], BigInt) = {
    val e16 = pushLefttime[T](ys, w)
    val ir = {
      val (q, scheds) = e16._1
      ((q, scheds), BigInt(6) + e16._2)
    }
    val ir34 = ir._1
    val ir40 = ir34._1
    val e23 = Paytime[T](ir40, ir34._2)
    (Conqueue3[T](ir40, e23._1), (BigInt(4) + e23._2) + ir._2)
  }
  
}

object ConList {
  
}

object Stream {
  def gettime[T](thiss : Conqueue.Stream2[T]): (Conqueue.ConList2[T], BigInt) = {
    val bd6 = thiss match {
      case Conqueue.Susp1(f130) =>
        val lr5 = lookup[Conqueue.ConList2[T]](List(6418, thiss))
        val mc17 = if (lr5._1) {
          (lr5._2, BigInt(1))
        } else {
          val e158 = fvaltime[T](thiss)
          (update[Conqueue.ConList2[T]](List(6418, thiss), e158._1), BigInt(3) + e158._2)
        }
        (mc17._1, BigInt(3) + mc17._2)
      case Conqueue.Val1(x419) =>
        (x419, BigInt(4))
    }
    (bd6._1, bd6._2)
  }
  
  def fvaltime[T](thiss : Conqueue.Stream2[T]): (Conqueue.ConList2[T], BigInt) = {
    val bd9 = {
      val Conqueue.Susp1(f133) = thiss
      val e175 = f133()
      (e175._1, BigInt(4) + e175._2)
    }
    (bd9._1, bd9._2)
  }
}
