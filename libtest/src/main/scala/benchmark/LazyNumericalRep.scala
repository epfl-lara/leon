package LazyNumericalRep

import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._

object DigitObject {
  abstract class Digit
  
  case class Zero() extends Digit
  
  case class One() extends Digit
}

object LazyNumericalRep {

  abstract class NumList2
  
  case class Tip1() extends NumList2
  
  case class Spine1(head12 : DigitObject.Digit, rear21 : NumStream2) extends NumList2
  
  abstract class NumStream2
  
  case class Val1(x324 : NumList2) extends NumStream2
  
  case class Susp1(fun3 : () => (NumList2, BigInt)) extends NumStream2
  
  case class Number2(digs1 : NumStream2, schedule1 : List[NumStream2])
  
  @invisibleBody
  def inctime(xs : NumStream2): (NumList2, BigInt) = {
    val e26 = NumStream.gettime(xs)
    val scr20 = BigInt(1) + e26._2
    val bd1 = e26._1 match {
      case Tip1() =>
        (Spine1(DigitObject.One(), xs), BigInt(4) + scr20)
      case s76 @ Spine1(DigitObject.Zero(), rear24) =>
        (Spine1(DigitObject.One(), rear24), BigInt(8) + scr20)
      case s77 @ Spine1(_, _) =>
        val e32 = incLazytime(xs)
        (e32._1, (BigInt(7) + e32._2) + scr20)
    }
    (bd1._1, bd1._2)
  }
  
  @invisibleBody
  @invstate
  def incLazytime(xs : NumStream2): (NumList2, BigInt) = {
    val e36 = NumStream.gettime(xs)
    val bd4 = {
      val Spine1(head, rear34) = e36._1
      val ir7 = DigitObject.One()
      val e38 = NumStream.gettime(rear34)
      val scr14 = BigInt(1) + e38._2
      val r163 = e38._1 match {
        case Tip1() =>
          (Spine1(DigitObject.Zero(), Val1(Spine1(ir7, rear34))), BigInt(6) + scr14)
        case Spine1(DigitObject.Zero(), srearfun1) =>
          (Spine1(DigitObject.Zero(), Val1(Spine1(ir7, srearfun1))), BigInt(10) + scr14)
        case s78 =>
          (Spine1(DigitObject.Zero(), Susp1(() => {
            val e51 = incLazytime(rear34)
            (e51._1, BigInt(1) + e51._2)
          })), BigInt(9) + scr14)
      }
      (r163._1, (BigInt(7) + r163._2) + e36._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def incNumtime(w : Number2): ((NumStream2, List[NumStream2]), BigInt) = {
    val e62 = inctime(w.digs1)
    val e96 = e62._1
    val ir6 = e96 match {
      case Spine1(DigitObject.Zero(), rear41 : Susp1) =>
        (Cons[NumStream2](rear41, w.schedule1), BigInt(8))
      case _ =>
        (w.schedule1, BigInt(7))
    }
    ((Val1(e96), ir6._1), (BigInt(6) + ir6._2) + e62._2)
  }
  
  @invisibleBody
  def Paytime[T](q : NumStream2, scheds : List[NumStream2]): (List[NumStream2], BigInt) = {
    val bd6 = scheds match {
      case c9 @ Cons(head16, rest10) =>
        val e57 = NumStream.gettime(head16)
        val scr10 = BigInt(1) + e57._2
        val mc13 = e57._1 match {
          case Spine1(DigitObject.Zero(), rear39 : Susp1) =>
            (Cons[NumStream2](rear39, rest10), BigInt(7) + scr10)
          case _ =>
            (rest10, BigInt(6) + scr10)
        }
        (mc13._1, BigInt(4) + mc13._2)
      case Nil() =>
        (scheds, BigInt(3))
    }
    (bd6._1, bd6._2)
  }
  
  @invisibleBody
  def incAndPaytime(w : Number2): (Number2, BigInt) = {
    val e15 = incNumtime(w)
    val ir = {
      val (q, scheds) = e15._1
      ((q, scheds), BigInt(6) + e15._2)
    }
    val ir12 = ir._1
    val ir18 = ir12._1
    val e22 = Paytime[BigInt](ir18, ir12._2)
    (Number2(ir18, e22._1), (BigInt(8) + e22._2) + ir._2)
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

object NumList {
  
}

object NumStream {
  def fvaltime(thiss : LazyNumericalRep.NumStream2): (LazyNumericalRep.NumList2, BigInt) = {
    val bd2 = {
      val LazyNumericalRep.Susp1(f120) = thiss
      val e34 = f120()
      (e34._1, BigInt(4) + e34._2)
    }
    (bd2._1, bd2._2)
  }
  
  def gettime(thiss : LazyNumericalRep.NumStream2): (LazyNumericalRep.NumList2, BigInt) = {
    val bd5 = thiss match {
      case LazyNumericalRep.Susp1(f121) =>
        val lr = lookup[LazyNumericalRep.NumList2](List(5299, thiss))
        val mc9 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e55 = fvaltime(thiss)
          (update[LazyNumericalRep.NumList2](List(5299, thiss), e55._1), BigInt(3) + e55._2)
        }
        (mc9._1, BigInt(3) + mc9._2)
      case LazyNumericalRep.Val1(x326) =>
        (x326, BigInt(4))
    }
    (bd5._1, bd5._2)
  }
}

object Number {
  
}
