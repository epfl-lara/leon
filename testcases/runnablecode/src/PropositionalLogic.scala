import scala.collection.immutable.Set
import leon.invariant._
import leon.instrumentation._
import leon.stats._
import org.sameersingh.scalaplot.Implicits._

object PropositionalLogic {
  abstract class Formula
  
  case class And(lhs : Formula, rhs : Formula) extends Formula
  
  case class Or(lhs : Formula, rhs : Formula) extends Formula
  
  case class Implies(lhs : Formula, rhs : Formula) extends Formula
  
  case class Not(f : Formula) extends Formula
  
  case class Literal(id : BigInt) extends Formula
  
  case class True() extends Formula
  
  case class False() extends Formula
  
  case class Pair(f : Formula, b : Boolean)
  
  abstract class List
  
  case class Cons(x : Pair, xs : List) extends List
  
  case class Nil() extends List
  
  def size(f : Formula): BigInt = f match {
    case And(lhs, rhs) =>
      (size(lhs) + size(rhs)) + BigInt(1)
    case Or(lhs, rhs) =>
      (size(lhs) + size(rhs)) + BigInt(1)
    case Implies(lhs, rhs) =>
      (size(lhs) + size(rhs)) + BigInt(1)
    case Not(f) =>
      size(f) + BigInt(1)
    case _ =>
      BigInt(1)
  }
  
  def removeImpliestime(f : Formula): (Formula, BigInt) = {
    val bd = f match {
      case And(lhs, rhs) =>
        val e19 = removeImpliestime(lhs)
        val e17 = removeImpliestime(rhs)
        (And(e19._1, e17._1), (BigInt(7) + e17._2) + e19._2)
      case Or(lhs, rhs) =>
        val e25 = removeImpliestime(lhs)
        val e23 = removeImpliestime(rhs)
        (Or(e25._1, e23._1), (BigInt(8) + e23._2) + e25._2)
      case Implies(lhs, rhs) =>
        val e32 = removeImpliestime(lhs)
        val e29 = removeImpliestime(rhs)
        (Or(Not(e32._1), e29._1), (BigInt(10) + e29._2) + e32._2)
      case Not(f) =>
        val e35 = removeImpliestime(f)
        (Not(e35._1), BigInt(8) + e35._2)
      case _ =>
        (f, BigInt(5))
    }
    (bd._1, bd._2)
  }
  
  def nnftime(formula : Formula): (Formula, BigInt) = {
    val bd3 = formula match {
      case And(lhs, rhs) =>
        val e78 = nnftime(lhs)
        val e76 = nnftime(rhs)
        (And(e78._1, e76._1), (BigInt(7) + e76._2) + e78._2)
      case Or(lhs, rhs) =>
        val e84 = nnftime(lhs)
        val e82 = nnftime(rhs)
        (Or(e84._1, e82._1), (BigInt(8) + e82._2) + e84._2)
      case Implies(lhs, rhs) =>
        val e90 = nnftime(lhs)
        val e88 = nnftime(rhs)
        (Implies(e90._1, e88._1), (BigInt(9) + e88._2) + e90._2)
      case Not(And(lhs, rhs)) =>
        val e97 = nnftime(Not(lhs))
        val e94 = nnftime(Not(rhs))
        (Or(e97._1, e94._1), (BigInt(14) + e94._2) + e97._2)
      case Not(Or(lhs, rhs)) =>
        val e105 = nnftime(Not(lhs))
        val e102 = nnftime(Not(rhs))
        (And(e105._1, e102._1), (BigInt(17) + e102._2) + e105._2)
      case Not(Implies(lhs, rhs)) =>
        val e113 = nnftime(lhs)
        val e110 = nnftime(Not(rhs))
        (And(e113._1, e110._1), (BigInt(19) + e110._2) + e113._2)
      case Not(Not(f)) =>
        val e115 = nnftime(f)
        (e115._1, BigInt(18) + e115._2)
      case Not(Literal(_)) =>
        (formula, BigInt(19))
      case Literal(_) =>
        (formula, BigInt(20))
      case Not(True()) =>
        (False(), BigInt(24))
      case Not(False()) =>
        (True(), BigInt(27))
      case _ =>
        (formula, BigInt(26))
    }
    (bd3._1, bd3._2)
  }
  
  def isNNFtime(f : Formula): (Boolean, BigInt) = {
    val bd1 = f match {
      case And(lhs, rhs) =>
        val e41 = isNNFtime(lhs)
        val e39 = isNNFtime(rhs)
        (e41._1 && e39._1, (BigInt(7) + e39._2) + e41._2)
      case Or(lhs, rhs) =>
        val e47 = isNNFtime(lhs)
        val e45 = isNNFtime(rhs)
        (e47._1 && e45._1, (BigInt(8) + e45._2) + e47._2)
      case Implies(lhs, rhs) =>
        (false, BigInt(6))
      case Not(Literal(_)) =>
        (true, BigInt(7))
      case Not(_) =>
        (false, BigInt(8))
      case _ =>
        (true, BigInt(8))
    }
    (bd1._1, bd1._2)
  }
  
  def simplifytime(f : Formula): (Formula, BigInt) = {
    val bd2 = f match {
      case And(lhs, rhs) =>
        val e49 = simplifytime(lhs)
        val e162 = e49._1
        val e51 = simplifytime(rhs)
        val e164 = e51._1
        val r159 = (e162, e164) match {
          case (False(), _) =>
            (False(), BigInt(6))
          case (_, False()) =>
            (False(), BigInt(9))
          case (True(), _) =>
            (e164, BigInt(11))
          case (_, True()) =>
            (e162, BigInt(14))
          case _ =>
            (And(e162, e164), BigInt(15))
        }
        (r159._1, ((BigInt(8) + r159._2) + e51._2) + e49._2)
      case Or(lhs, rhs) =>
        val e57 = simplifytime(lhs)
        val e166 = e57._1
        val e59 = simplifytime(rhs)
        val e168 = e59._1
        val r161 = (e166, e168) match {
          case (True(), _) =>
            (True(), BigInt(6))
          case (_, True()) =>
            (True(), BigInt(9))
          case (False(), _) =>
            (e168, BigInt(11))
          case (_, False()) =>
            (e166, BigInt(14))
          case _ =>
            (Or(e166, e168), BigInt(15))
        }
        (r161._1, ((BigInt(9) + r161._2) + e59._2) + e57._2)
      case Implies(lhs, rhs) =>
        val e65 = simplifytime(lhs)
        val e170 = e65._1
        val e67 = simplifytime(rhs)
        val e172 = e67._1
        val r163 = (e170, e172) match {
          case (False(), _) =>
            (True(), BigInt(6))
          case (_, True()) =>
            (True(), BigInt(9))
          case (True(), _) =>
            (e172, BigInt(11))
          case (_, False()) =>
            (Not(e170), BigInt(15))
          case _ =>
            (Implies(e170, e172), BigInt(15))
        }
        (r163._1, ((BigInt(10) + r163._2) + e67._2) + e65._2)
      case Not(True()) =>
        (False(), BigInt(8))
      case Not(False()) =>
        (True(), BigInt(11))
      case _ =>
        (f, BigInt(10))
    }
    (bd2._1, bd2._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(2*_ + 1)
    val orbTime = size.map(43*_ - 17)
    var operTime = List[Int]()
    var realTime = List[Long]()
    ((10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)).foreach { i =>
      val form = {
        (1 to i).foldLeft[Formula](Literal(1)) { (f, n) =>
          if(n%2 == 0) And(f, Literal(1)) else Or(f, Literal(1))
        }
      }
      operTime :+ (timed{ nnftime(form) }{realTime :+ _})._2
    }
    println(orbTime)
    println(operTime)
    println(realTime)

//    val char = xyChart(List(size -> (orbTime, operTime, realTime)))
  }
}
