import leon.instrumentation._
import leon.collection._
import leon.lang._
import leon.collection.ListSpecs._
import leon.annotation._
import leon.invariant._

object ConcTrees {
  abstract class Conc[T]
  
  case class Empty[T]() extends Conc[T]
  
  case class Single[T](x : T) extends Conc[T]
  
  case class CC[T](left : Conc[T], right : Conc[T]) extends Conc[T]
  
  def abs(x : BigInt): BigInt = if (x < BigInt(0)) {
    -x
  } else {
    x
  }
  
  @invisibleBody
  def lookuptime[T](xs : Conc[T], i : BigInt): (T, BigInt) = {
    val bd4 = xs match {
      case Single(x) =>
        (x, BigInt(3))
      case CC(l, r) =>
        val c48 = BigInt(2)
        val expr8 = if (i < Conc.sizetime[T](l)._1) {
          val e206 = lookuptime[T](l, i)
          (e206._1, (BigInt(2) + c48) + e206._2)
        } else {
          val e209 = lookuptime[T](r, i - Conc.sizetime[T](l)._1)
          (e209._1, (BigInt(4) + c48) + e209._2)
        }
        (expr8._1, BigInt(5) + expr8._2)
    }
    bd4
  }
  
  @invisibleBody
  def instAppendIndexAxiom[T](xs : Conc[T], i : BigInt): Boolean = xs match {
    case CC(l, r) =>
      appendIndex[T](Conc.toList[T](l), Conc.toList[T](r), i)
    case _ =>
      true
  }
  
  @invisibleBody
  def updatetime[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd2 = xs match {
      case Single(x) =>
        (Single[T](y), BigInt(4))
      case CC(l, r) =>
        val c38 = BigInt(2)
        val expr6 = if (i < Conc.sizetime[T](l)._1) {
          val e140 = updatetime[T](l, i, y)
          (CC[T](e140._1, r), (BigInt(3) + c38) + e140._2)
        } else {
          val e146 = updatetime[T](r, i - Conc.sizetime[T](l)._1, y)
          (CC[T](l, e146._1), (BigInt(5) + c38) + e146._2)
        }
        (expr6._1, BigInt(5) + expr6._2)
    }
    bd2
  }
  
  @invisibleBody
  def instAppendUpdateAxiom[T](xs : Conc[T], i : BigInt, y : T): Boolean = xs match {
    case CC(l, r) =>
      appendUpdate[T](Conc.toList[T](l), Conc.toList[T](r), i, y)
    case _ =>
      true
  }
  
  @invisibleBody
  def concatNonEmptytime[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val ir25 = Conc.leveltime[T](ys)._1 - Conc.leveltime[T](xs)._1
    val c50 = BigInt(3)
    val r187 = if (ir25 >= BigInt(-1) && ir25 <= BigInt(1)) {
      (CC[T](xs, ys), BigInt(2) + c50)
    } else {
      val el1 = if (ir25 < BigInt(-1)) {
        val c54 = BigInt(9)
        val th2 = if (xs.isInstanceOf[CC[T]] && Conc.leveltime[T](xs.asInstanceOf[CC[T]].left)._1 >= Conc.leveltime[T](xs.asInstanceOf[CC[T]].right)._1) {
          val e34 = concatNonEmptytime[T](xs.asInstanceOf[CC[T]].right, ys)
          (CC[T](xs.asInstanceOf[CC[T]].left, e34._1), (BigInt(7) + c54) + e34._2)
        } else {
          val el3 = if (xs.isInstanceOf[CC[T]]) {
            val th4 = {
              val CC(rl, rr) = xs.asInstanceOf[CC[T]].right
              val e41 = concatNonEmptytime[T](rr, ys)
              val e465 = e41._1
              val c58 = BigInt(4)
              val r188 = if (Conc.leveltime[T](e465)._1 == Conc.leveltime[T](xs)._1 - BigInt(3)) {
                (CC[T](xs.asInstanceOf[CC[T]].left, CC[T](rl, e465)), BigInt(5) + c58)
              } else {
                (CC[T](CC[T](xs.asInstanceOf[CC[T]].left, rl), e465), BigInt(5) + c58)
              }
              (r188._1, (BigInt(8) + r188._2) + e41._2)
            }
            (th4._1, BigInt(2) + th4._2)
          } else {
            (error[CC[T]]("Match is non-exhaustive"), BigInt(2))
          }
          (el3._1, (BigInt(1) + c54) + el3._2)
        }
        (th2._1, BigInt(2) + th2._2)
      } else {
        val c60 = BigInt(9)
        val el2 = if (ys.isInstanceOf[CC[T]] && Conc.leveltime[T](ys.asInstanceOf[CC[T]].right)._1 >= Conc.leveltime[T](ys.asInstanceOf[CC[T]].left)._1) {
          val e84 = concatNonEmptytime[T](xs, ys.asInstanceOf[CC[T]].left)
          (CC[T](e84._1, ys.asInstanceOf[CC[T]].right), (BigInt(7) + c60) + e84._2)
        } else {
          val el6 = if (ys.isInstanceOf[CC[T]]) {
            val th7 = {
              val CC(ll, lr) = ys.asInstanceOf[CC[T]].left
              val e89 = concatNonEmptytime[T](xs, ll)
              val e523 = e89._1
              val c64 = BigInt(4)
              val r193 = if (Conc.leveltime[T](e523)._1 == Conc.leveltime[T](ys)._1 - BigInt(3)) {
                (CC[T](CC[T](e523, lr), ys.asInstanceOf[CC[T]].right), BigInt(5) + c64)
              } else {
                (CC[T](e523, CC[T](lr, ys.asInstanceOf[CC[T]].right)), BigInt(5) + c64)
              }
              (r193._1, (BigInt(8) + r193._2) + e89._2)
            }
            (th7._1, BigInt(2) + th7._2)
          } else {
            (error[CC[T]]("Match is non-exhaustive"), BigInt(2))
          }
          (el6._1, (BigInt(1) + c60) + el6._2)
        }
        (el2._1, BigInt(2) + el2._2)
      }
      (el1._1, (BigInt(1) + c50) + el1._2)
    }
    (r187._1, BigInt(4) + r187._2)
  }
  
  @invisibleBody
  def appendAssocInst[T](xs : Conc[T], ys : Conc[T]): Boolean = (xs match {
    case CC(l, r) =>
      appendAssoc[T](Conc.toList[T](l), Conc.toList[T](r), Conc.toList[T](ys)) && (r match {
        case CC(rl, rr) =>
          appendAssoc[T](Conc.toList[T](rl), Conc.toList[T](rr), Conc.toList[T](ys)) && appendAssoc[T](Conc.toList[T](l), Conc.toList[T](rl), Conc.toList[T](rr).++(Conc.toList[T](ys)))
        case _ =>
          true
      })
    case _ =>
      true
  }) && (ys match {
    case CC(l, r) =>
      appendAssoc[T](Conc.toList[T](xs), Conc.toList[T](l), Conc.toList[T](r)) && (l match {
        case CC(ll, lr) =>
          appendAssoc[T](Conc.toList[T](xs), Conc.toList[T](ll), Conc.toList[T](lr)) && appendAssoc[T](Conc.toList[T](xs).++(Conc.toList[T](ll)), Conc.toList[T](lr), Conc.toList[T](r))
        case _ =>
          true
      })
    case _ =>
      true
  })
  
  @invisibleBody
  def concatNormalizedtime[T](xs : Conc[T], ys : Conc[T]): (Conc[T], BigInt) = {
    val bd7 = (xs, ys) match {
      case (xs, Empty()) =>
        (xs, BigInt(6))
      case (Empty(), ys) =>
        (ys, BigInt(9))
      case _ =>
        val e272 = concatNonEmptytime[T](xs, ys)
        (e272._1, BigInt(9) + e272._2)
    }
    bd7
  }
  
  @invisibleBody
  def concatCorrectness[T](res : Conc[T], xs : Conc[T], ys : Conc[T]): Boolean = Conc.toList[T](res) == Conc.toList[T](xs).++(Conc.toList[T](ys))
  
  @invisibleBody
  def inserttime[T](xs : Conc[T], i : BigInt, y : T): (Conc[T], BigInt) = {
    val bd3 = if (xs.isInstanceOf[Empty[T]]) {
      (Single[T](y), BigInt(3))
    } else {
      val el10 = if (xs.isInstanceOf[Single[T]]) {
        val th11 = if (i == BigInt(0)) {
          (CC[T](Single[T](y), xs), BigInt(4))
        } else {
          (CC[T](xs, Single[T](y)), BigInt(4))
        }
        (th11._1, BigInt(2) + th11._2)
      } else {
        val c34 = BigInt(6)
        val el11 = if (xs.isInstanceOf[CC[T]] && i < Conc.sizetime[T](xs.asInstanceOf[CC[T]].left)._1) {
          val e172 = inserttime[T](xs.asInstanceOf[CC[T]].left, i, y)
          val e166 = concatNonEmptytime[T](e172._1, xs.asInstanceOf[CC[T]].right)
          (e166._1, ((BigInt(7) + c34) + e166._2) + e172._2)
        } else {
          val el13 = if (xs.isInstanceOf[CC[T]]) {
            val e181 = inserttime[T](xs.asInstanceOf[CC[T]].right, i - Conc.sizetime[T](xs.asInstanceOf[CC[T]].left)._1, y)
            val e177 = concatNonEmptytime[T](xs.asInstanceOf[CC[T]].left, e181._1)
            (e177._1, (BigInt(12) + e177._2) + e181._2)
          } else {
            (error[Conc[T]]("Match is non-exhaustive"), BigInt(2))
          }
          (el13._1, (BigInt(1) + c34) + el13._2)
        }
        (el11._1, BigInt(2) + el11._2)
      }
      (el10._1, BigInt(2) + el10._2)
    }
    bd3
  }
  
  @invisibleBody
  def insertAtIndex[T](l : List[T], i : BigInt, y : T): List[T] = l match {
    case Nil() =>
      List[T](y)
    case _ if i == BigInt(0) =>
      Cons[T](y, l)
    case Cons(x, tail) =>
      Cons[T](x, insertAtIndex[T](tail, i - BigInt(1), y))
  }
  
  @invisibleBody
  def appendInsertIndex[T](l1 : List[T], l2 : List[T], i : BigInt, y : T): Boolean = (l1 match {
    case Nil() =>
      true
    case Cons(x, xs) =>
      if (i == BigInt(0)) {
        true
      } else {
        appendInsertIndex[T](xs, l2, i - BigInt(1), y)
      }
  }) && insertAtIndex[T](l1.++(l2), i, y) == (if (i < l1.size) {
    insertAtIndex[T](l1, i, y).++(l2)
  } else {
    l1.++(insertAtIndex[T](l2, i - l1.size, y))
  })
  
  @invisibleBody
  def insertAppendAxiomInst[T](xs : Conc[T], i : BigInt, y : T): Boolean = xs match {
    case CC(l, r) =>
      appendInsertIndex[T](Conc.toList[T](l), Conc.toList[T](r), i, y)
    case _ =>
      true
  }
  
  @invisibleBody
  def splittime[T](xs : Conc[T], n : BigInt): ((Conc[T], Conc[T]), BigInt) = {
    val bd5 = xs match {
      case Empty() =>
        ((Empty[T](), Empty[T]()), BigInt(5))
      case s @ Single(x) =>
        val expr10 = if (n <= BigInt(0)) {
          ((Empty[T](), s), BigInt(4))
        } else {
          ((s, Empty[T]()), BigInt(4))
        }
        (expr10._1, BigInt(4) + expr10._2)
      case CC(l, r) =>
        val c42 = BigInt(2)
        val expr11 = if (n < Conc.sizetime[T](l)._1) {
          val e230 = splittime[T](l, n)
          val ir3 = {
            val (ll, lr) = e230._1
            ((ll, lr), BigInt(6) + e230._2)
          }
          val ir9 = ir3._1
          val e237 = concatNormalizedtime[T](ir9._2, r)
          ((ir9._1, e237._1), ((BigInt(8) + c42) + e237._2) + ir3._2)
        } else {
          val c44 = BigInt(2)
          val el17 = if (n > Conc.sizetime[T](l)._1) {
            val e242 = splittime[T](r, n - Conc.sizetime[T](l)._1)
            val ir6 = {
              val (rl, rr) = e242._1
              ((rl, rr), BigInt(8) + e242._2)
            }
            val ir15 = ir6._1
            val e253 = concatNormalizedtime[T](l, ir15._1)
            ((e253._1, ir15._2), ((BigInt(8) + c44) + e253._2) + ir6._2)
          } else {
            ((l, r), BigInt(2) + c44)
          }
          (el17._1, (BigInt(1) + c42) + el17._2)
        }
        (expr11._1, BigInt(6) + expr11._2)
    }
    bd5
  }
  
  @invisibleBody
  def splitCorrectness[T](r : (Conc[T], Conc[T]), xs : Conc[T], n : BigInt): Boolean = Conc.toList[T](r._1) == Conc.toList[T](xs).take(n) && Conc.toList[T](r._2) == Conc.toList[T](xs).drop(n)
  
  @invisibleBody
  def instSplitAxiom[T](xs : Conc[T], n : BigInt): Boolean = xs match {
    case CC(l, r) =>
      appendTakeDrop[T](Conc.toList[T](l), Conc.toList[T](r), n)
    case _ =>
      true
  }
}

object Conc {
  def leveltime[T](thiss : ConcTrees.Conc[T]): (BigInt, BigInt) = {
    val bd = thiss match {
      case ConcTrees.Empty() =>
        (BigInt(0), BigInt(2))
      case ConcTrees.Single(x) =>
        (BigInt(0), BigInt(4))
      case ConcTrees.CC(l, r) =>
        val c46 = BigInt(3)
        val e11 = if (leveltime[T](l)._1 >= leveltime[T](r)._1) {
          (leveltime[T](l)._1, BigInt(2) + c46)
        } else {
          (leveltime[T](r)._1, BigInt(2) + c46)
        }
        (BigInt(1) + e11._1, BigInt(7) + e11._2)
    }
    bd
  }
  
  def balanced[T](thiss : ConcTrees.Conc[T]): Boolean = thiss match {
    case ConcTrees.CC(l, r) =>
      leveltime[T](l)._1 - leveltime[T](r)._1 >= BigInt(-1) && leveltime[T](l)._1 - leveltime[T](r)._1 <= BigInt(1) && balanced[T](l) && balanced[T](r)
    case _ =>
      true
  }
  
  def concInv[T](thiss : ConcTrees.Conc[T]): Boolean = thiss match {
    case ConcTrees.CC(l, r) =>
      !isEmpty[T](l) && !isEmpty[T](r) && concInv[T](l) && concInv[T](r)
    case _ =>
      true
  }
  
  def isLeaf[T](thiss : ConcTrees.Conc[T]): Boolean = thiss match {
    case ConcTrees.Empty() =>
      true
    case ConcTrees.Single(_) =>
      true
    case _ =>
      false
  }
  
  def isEmpty[T](thiss : ConcTrees.Conc[T]): Boolean = thiss == ConcTrees.Empty[T]()
  
  def sizetime[T](thiss : ConcTrees.Conc[T]): (BigInt, BigInt) = {
    val bd6 = thiss match {
      case ConcTrees.Empty() =>
        (BigInt(0), BigInt(2))
      case ConcTrees.Single(x) =>
        (BigInt(1), BigInt(4))
      case ConcTrees.CC(l, r) =>
        (sizetime[T](l)._1 + sizetime[T](r)._1, BigInt(9))
    }
    bd6
  }
  
  @invisibleBody
  def toList[T](thiss : ConcTrees.Conc[T]): List[T] = thiss match {
    case ConcTrees.Empty() =>
      List[T]()
    case ConcTrees.Single(x) =>
      List[T](x)
    case ConcTrees.CC(l, r) =>
      toList[T](l).++(toList[T](r))
  }
}
