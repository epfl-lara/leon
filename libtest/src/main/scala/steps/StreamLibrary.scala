package StreamLibrary

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._

object StreamLibrary {
  
  abstract class LList2
  
  
  case class SCons1(x327 : BigInt, tailFun2 : () => (LList2, BigInt)) extends LList2
  
  
  case class SNil1() extends LList2
  
  def natsFromntime(n : BigInt): (LList2, BigInt) = (SCons1(n, () => {
    val e49 = genNextNatFromtime(n)
    (e49._1, BigInt(1) + e49._2)
  }), BigInt(2))
  
  def genNextNatFromtime(n : BigInt): (LList2, BigInt) = {
    val ir13 = BigInt(1) + n
    (SCons1(ir13, () => {
      val e164 = genNextNatFromtime(ir13)
      (e164._1, BigInt(1) + e164._2)
    }), BigInt(3))
  }
  
  @extern
  def constFun1time(n : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  def maptime(f : (BigInt) => (BigInt, BigInt), s : LList2): (LList2, BigInt) = {
    val bd26 = s match {
      case SNil1() =>
        (SNil1(), BigInt(3))
      case l43 @ SCons1(x, _) =>
        val e146 = f(x)
        (SCons1(e146._1, () => {
          val e150 = mapSusptime(f, s)
          (e150._1, BigInt(1) + e150._2)
        }), BigInt(7) + e146._2)
    }
    (bd26._1, bd26._2)
  }
  
  def mapSusptime(f : (BigInt) => (BigInt, BigInt), s : LList2): (LList2, BigInt) = {
    val e57 = LList.tailOrNiltime(s)
    val e59 = maptime(f, e57._1)
    (e59._1, (BigInt(2) + e59._2) + e57._2)
  }
  
  def appendListtime(l : List[BigInt], s : LList2): (LList2, BigInt) = {
    val bd37 = l match {
      case Nil() =>
        (s, BigInt(2))
      case Cons(x, tail) =>
        (SCons1(x, () => {
          val e201 = appendListtime(tail, s)
          (e201._1, BigInt(1) + e201._2)
        }), BigInt(7))
    }
    (bd37._1, bd37._2)
  }
  
  def repeattime(n : BigInt): (LList2, BigInt) = (SCons1(n, () => {
    val e53 = repeattime(n)
    (e53._1, BigInt(1) + e53._2)
  }), BigInt(2))
  
  def cycletime(l : List[BigInt]): (LList2, BigInt) = {
    val bd40 = l match {
      case Nil() =>
        (SNil1(), BigInt(3))
      case Cons(x, t) =>
        (SCons1(x, () => {
          val e215 = cycletime(l)
          val e217 = appendListtime(t, e215._1)
          (e217._1, (BigInt(2) + e217._2) + e215._2)
        }), BigInt(7))
    }
    (bd40._1, bd40._2)
  }
  
  @extern
  def constFun2time(n : BigInt): (Boolean, BigInt) = ((true, 1) : (Boolean, BigInt))
  
  def takeWhiletime(p : (BigInt) => (Boolean, BigInt), s : LList2): (LList2, BigInt) = {
    val bd28 = s match {
      case SNil1() =>
        (SNil1(), BigInt(3))
      case l44 @ SCons1(x, _) =>
        val e159 = p(x)
        val c19 = BigInt(1) + e159._2
        val mc17 = if (e159._1) {
          (SCons1(x, () => {
            val e155 = takeWhileSusptime(p, s)
            (e155._1, BigInt(1) + e155._2)
          }), BigInt(3) + c19)
        } else {
          (SNil1(), BigInt(2) + c19)
        }
        (mc17._1, BigInt(4) + mc17._2)
    }
    (bd28._1, bd28._2)
  }
  
  def takeWhileSusptime(p : (BigInt) => (Boolean, BigInt), s : LList2): (LList2, BigInt) = {
    val e195 = LList.tailOrNiltime(s)
    val e197 = takeWhiletime(p, e195._1)
    (e197._1, (BigInt(2) + e197._2) + e195._2)
  }
  
  @extern
  def constFun3time(n : BigInt, m : BigInt): (BigInt, BigInt) = ((0, 1) : (BigInt, BigInt))
  
  def scantime(f : (BigInt, BigInt) => (BigInt, BigInt), z : BigInt, s : LList2): (LList2, BigInt) = {
    val bd17 = s match {
      case SNil1() =>
        (SNil1(), BigInt(3))
      case l42 @ SCons1(x, _) =>
        val e102 = f(z, x)
        val e346 = e102._1
        (SCons1(z, () => {
          val e107 = scanSusptime(f, e346, s)
          (e107._1, BigInt(1) + e107._2)
        }), BigInt(7) + e102._2)
    }
    (bd17._1, bd17._2)
  }
  
  def scanSusptime(f : (BigInt, BigInt) => (BigInt, BigInt), z : BigInt, s : LList2): (LList2, BigInt) = {
    val e141 = LList.tailOrNiltime(s)
    val e143 = scantime(f, z, e141._1)
    (e143._1, (BigInt(2) + e143._2) + e141._2)
  }
  
  @extern
  def constFun4time(n : BigInt): ((BigInt, BigInt), BigInt) = (((0, 0), 1) : ((BigInt, BigInt), BigInt))
  
  def unfoldtime(f : (BigInt) => ((BigInt, BigInt), BigInt), c : BigInt): (LList2, BigInt) = {
    val e221 = f(c)
    val ir2 = {
      val (x, d) = e221._1
      ((x, d), BigInt(6) + e221._2)
    }
    val ir5 = ir2._1
    val ir12 = ir5._2
    (SCons1(ir5._1, () => {
      val e229 = unfoldtime(f, ir12)
      (e229._1, BigInt(1) + e229._2)
    }), BigInt(4) + ir2._2)
  }
  
  def isPrefixOftime(l : List[BigInt], s : LList2): (Boolean, BigInt) = {
    val bd33 = s match {
      case SNil1() =>
        val mc23 = l match {
          case Nil() =>
            (true, BigInt(2))
          case _ =>
            (false, BigInt(2))
        }
        (mc23._1, BigInt(2) + mc23._2)
      case ss1 @ SCons1(x, _) =>
        val mc26 = l match {
          case Nil() =>
            (true, BigInt(2))
          case ll @ Cons(y, tail) =>
            val mc25 = if (x == y) {
              val e179 = LList.tailOrNiltime(s)
              val e181 = isPrefixOftime(tail, e179._1)
              (e181._1, (BigInt(4) + e181._2) + e179._2)
            } else {
              (false, BigInt(2))
            }
            (mc25._1, BigInt(5) + mc25._2)
        }
        (mc26._1, BigInt(4) + mc26._2)
    }
    (bd33._1, bd33._2)
  }
  
  def zipWithtime(f : (BigInt, BigInt) => (BigInt, BigInt), a : LList2, b : LList2): (LList2, BigInt) = {
    val bd3 = a match {
      case SNil1() =>
        (SNil1(), BigInt(3))
      case al1 @ SCons1(x, _) =>
        val mc3 = b match {
          case SNil1() =>
            (SNil1(), BigInt(3))
          case bl1 @ SCons1(y, _) =>
            val e31 = f(x, y)
            (SCons1(e31._1, () => {
              val e36 = zipWithSusptime(f, al1, bl1)
              (e36._1, BigInt(1) + e36._2)
            }), BigInt(7) + e31._2)
        }
        (mc3._1, BigInt(4) + mc3._2)
    }
    (bd3._1, bd3._2)
  }
  
  def zipWithSusptime(f : (BigInt, BigInt) => (BigInt, BigInt), a : LList2, b : LList2): (LList2, BigInt) = {
    val e83 = LList.tailOrNiltime(a)
    val e86 = LList.tailOrNiltime(b)
    val e88 = zipWithtime(f, e83._1, e86._1)
    (e88._1, ((BigInt(3) + e88._2) + e86._2) + e83._2)
  }
  
}

object LList {
  def tailtime(thiss : StreamLibrary.LList2): (StreamLibrary.LList2, BigInt) = {
    val bd32 = {
      val StreamLibrary.SCons1(_, tailFun3) = thiss
      val e176 = tailFun3()
      (e176._1, BigInt(4) + e176._2)
    }
    (bd32._1, bd32._2)
  }
  
  def tailOrNiltime(thiss : StreamLibrary.LList2): (StreamLibrary.LList2, BigInt) = {
    val bd21 = thiss match {
      case StreamLibrary.SNil1() =>
        (thiss, BigInt(2))
      case _ =>
        val lr = lookup[StreamLibrary.LList2](List(5025, thiss))
        val mc13 = if (lr._1) {
          (lr._2, BigInt(1))
        } else {
          val e129 = tailtime(thiss)
          (update[StreamLibrary.LList2](List(5025, thiss), e129._1), BigInt(3) + e129._2)
        }
        (mc13._1, BigInt(2) + mc13._2)
    }
    (bd21._1, bd21._2)
  }
}
