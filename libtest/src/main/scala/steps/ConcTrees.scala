package ConcTrees

import leon.collection._
import leon.instrumentation._
import leon.collection._
import leon.lang._
import leon.collection.ListSpecs._
import leon.annotation._
import leon.invariant._

object ConcTrees {
	@inline
  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
	
  abstract class Conc[T] {
  	val size: BigInt = {
		  (this match {
		    case Empty()   => 0
		    case Single(x) => 1
		    case CC(l, r) =>
		      l.size + r.size
		  }): BigInt
		} ensuring (_ >= 0)

		val level: BigInt = {
      (this match {
        case Empty()   => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)
  }
  
  case class Empty[T]() extends Conc[T]
  
  case class Single[T](x : T) extends Conc[T]
  
  case class CC[T](left : Conc[T], right : Conc[T]) extends Conc[T]
  
  @invisibleBody
  def lookuptime[T](xs : Conc[T], i : BigInt): (T, BigInt) = {
    val bd13 = xs match {
      case Single(x) =>
        (x, BigInt(3))
      case CC(l, r) =>
        val c40 = BigInt(2)
        val mc37 = if (i < (l.size)) {
          val e276 = lookuptime[T](l, i)
          (e276._1, (BigInt(2) + c40) + e276._2)
        } else {
          val e283 = lookuptime[T](r, i - (l.size))
          (e283._1, (BigInt(4) + c40) + e283._2)
        }
        (mc37._1, BigInt(5) + mc37._2)
    }
    (bd13._1, bd13._2)
  }
  
  @invisibleBody
  def updatetime[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd10 = xs match {
      case Single(x) =>
        (Single[T](y), BigInt(4))
      case CC(l, r) =>
        val c38 = BigInt(2)
        val mc27 = if (i < (l.size)) {
          val e180 = updatetime[T](l, i, y)
          (CC[T](e180._1, r), (BigInt(3) + c38) + e180._2)
        } else {
          val e191 = updatetime[T](r, i - (l.size), y)
          (CC[T](l, e191._1), (BigInt(5) + c38) + e191._2)
        }
        (mc27._1, BigInt(5) + mc27._2)
    }
    (bd10._1, bd10._2)
  }
  
  @invisibleBody
  def concatNonEmptytime[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val ir46 = (ys.level) - (xs.level)
    val c42 = BigInt(3)
    val r199 = if (ir46 >= BigInt(-1) && ir46 <= BigInt(1)) {
      (CC[T](xs, ys), BigInt(2) + c42)
    } else {
      val el5 = if (ir46 < BigInt(-1)) {
        val th3 = {
          val CC(l, r) = xs
          val c46 = BigInt(3)
          val mc2 = if ((l.level) >= (r.level)) {
            val e37 = concatNonEmptytime[T](r, ys)
            (CC[T](l, e37._1), (BigInt(3) + c46) + e37._2)
          } else {
            val el1 = {
              val CC(rl, rr) = r
              val e41 = concatNonEmptytime[T](rr, ys)
              val e440 = e41._1
              val c48 = BigInt(4)
              val r191 = if ((e440.level) == (xs.level) - BigInt(3)) {
                (CC[T](l, CC[T](rl, e440)), BigInt(3) + c48)
              } else {
                (CC[T](CC[T](l, rl), e440), BigInt(3) + c48)
              }
              (r191._1, (BigInt(5) + r191._2) + e41._2)
            }
            (el1._1, (BigInt(1) + c46) + el1._2)
          }
          (mc2._1, BigInt(4) + mc2._2)
        }
        (th3._1, BigInt(2) + th3._2)
      } else {
        val el4 = {
          val CC(l, r) = ys
          val c50 = BigInt(3)
          val mc4 = if ((r.level) >= (l.level)) {
            val e66 = concatNonEmptytime[T](xs, l)
            (CC[T](e66._1, r), (BigInt(3) + c50) + e66._2)
          } else {
            val el3 = {
              val CC(ll, lr) = l
              val e71 = concatNonEmptytime[T](xs, ll)
              val e460 = e71._1
              val c52 = BigInt(4)
              val r196 = if ((e460.level) == (ys.level) - BigInt(3)) {
                (CC[T](CC[T](e460, lr), r), BigInt(3) + c52)
              } else {
                (CC[T](e460, CC[T](lr, r)), BigInt(3) + c52)
              }
              (r196._1, (BigInt(5) + r196._2) + e71._2)
            }
            (el3._1, (BigInt(1) + c50) + el3._2)
          }
          (mc4._1, BigInt(4) + mc4._2)
        }
        (el4._1, BigInt(2) + el4._2)
      }
      (el5._1, (BigInt(1) + c42) + el5._2)
    }
    (r199._1, BigInt(3) + r199._2)
  }
  
  @invisibleBody
  def concatNormalizedtime[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val bd3 = (xs, ys) match {
      case (xs, Empty()) =>
        (xs, BigInt(6))
      case (Empty(), ys) =>
        (ys, BigInt(9))
      case _ =>
        val e119 = concatNonEmptytime[T](xs, ys)
        (e119._1, BigInt(9) + e119._2)
    }
    (bd3._1, bd3._2)
  }
  
  @invisibleBody
  def inserttime[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd11 = xs match {
      case Empty() =>
        (Single[T](y), BigInt(3))
      case Single(x) =>
        val mc29 = if (i == BigInt(0)) {
          (CC[T](Single[T](y), xs), BigInt(4))
        } else {
          (CC[T](xs, Single[T](y)), BigInt(4))
        }
        (mc29._1, BigInt(4) + mc29._2)
      case CC(l, r) =>
        val c36 = BigInt(2)
        val mc30 = if (i < (l.size)) {
          val e209 = inserttime[T](l, i, y)
          val e212 = concatNonEmptytime[T](e209._1, r)
          (e212._1, ((BigInt(3) + c36) + e212._2) + e209._2)
        } else {
          val e221 = inserttime[T](r, i - (l.size), y)
          val e223 = concatNonEmptytime[T](l, e221._1)
          (e223._1, ((BigInt(5) + c36) + e223._2) + e221._2)
        }
        (mc30._1, BigInt(6) + mc30._2)
    }
    (bd11._1, bd11._2)
  }
  
  @invisibleBody
  def splittime[T](xs : Conc[T], n : BigInt): ((Conc[T], Conc[T]), BigInt) = {
    val bd12 = xs match {
      case Empty() =>
        ((Empty[T](), Empty[T]()), BigInt(5))
      case s @ Single(x) =>
        val mc32 = if (n <= BigInt(0)) {
          ((Empty[T](), s), BigInt(4))
        } else {
          ((s, Empty[T]()), BigInt(4))
        }
        (mc32._1, BigInt(4) + mc32._2)
      case CC(l, r) =>
        val c30 = BigInt(2)
        val mc35 = if (n < (l.size)) {
          val e238 = splittime[T](l, n)
          val ir10 = {
            val (ll, lr) = e238._1
            ((ll, lr), BigInt(6) + e238._2)
          }
          val ir18 = ir10._1
          val e246 = concatNormalizedtime[T](ir18._2, r)
          ((ir18._1, e246._1), ((BigInt(5) + c30) + e246._2) + ir10._2)
        } else {
          val c32 = BigInt(2)
          val el12 = if (n > (l.size)) {
            val e254 = splittime[T](r, n - (l.size))
            val ir13 = {
              val (rl, rr) = e254._1
              ((rl, rr), BigInt(8) + e254._2)
            }
            val ir24 = ir13._1
            val e261 = concatNormalizedtime[T](l, ir24._1)
            ((e261._1, ir24._2), ((BigInt(5) + c32) + e261._2) + ir13._2)
          } else {
            ((l, r), BigInt(2) + c32)
          }
          (el12._1, (BigInt(1) + c30) + el12._2)
        }
        (mc35._1, BigInt(6) + mc35._2)
    }
    (bd12._1, bd12._2)
  }
}

object Conc {
  
}
