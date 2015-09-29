import scala.collection.immutable.Set
import leon.invariant._
import leon.instrumentation._

object PropositionalLogic {

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: BigInt) extends Formula
  case class True() extends Formula
  case class False() extends Formula

  case class Pair(f: Formula, b: Boolean)

  sealed abstract class List
  case class Cons(x: Pair, xs: List) extends List
  case class Nil() extends List

  def size(f : Formula) : BigInt = (f match {
    case And(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Or(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Implies(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Not(f) => size(f) + 1
    case _ => 1
  })

  def removeImplies(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(removeImplies(lhs), removeImplies(rhs))
    case Or(lhs, rhs) => Or(removeImplies(lhs), removeImplies(rhs))
    case Implies(lhs, rhs) => Or(Not(removeImplies(lhs)),removeImplies(rhs))
    case Not(f) => Not(removeImplies(f))
    case _ => f

  }) ensuring(_ => time <= ? * size(f) + ?)

  def nnf(formula: Formula): Formula = (formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Implies(lhs, rhs) => Implies(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
    case Not(True()) => False()
    case Not(False()) => True()
    case _ => formula
  }) ensuring(_ => time <= ? * size(formula) + ?)

  def isNNF(f: Formula): Boolean = { f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => false
    case Not(Literal(_)) => true
    case Not(_) => false
    case _ => true
  }} ensuring(_ => time <= ? * size(f) + ?)

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => {
      val sl = simplify(lhs)
      val sr = simplify(rhs)

      //if lhs or rhs is false, return false
      //if lhs is true return rhs
      //if rhs is true return lhs
      (sl,sr) match {
        case (False(), _) => False()
        case (_, False()) => False()
        case (True(), _) => sr
        case (_, True()) => sl
        case _ => And(sl, sr)
      }
    }
    case Or(lhs, rhs) => {
      val sl = simplify(lhs)
      val sr = simplify(rhs)

      //if lhs or rhs is true, return true
      //if lhs is false return rhs
      //if rhs is false return lhs
      (sl,sr) match {
        case (True(), _) => True()
        case (_, True()) => True()
        case (False(), _) => sr
        case (_, False()) => sl
        case _ => Or(sl, sr)
      }
    }
    case Implies(lhs, rhs) => {
      val sl = simplify(lhs)
      val sr = simplify(rhs)

      //if lhs is false return true
      //if rhs is true return true
      //if lhs is true return rhs
      //if rhs is false return Not(rhs)
      (sl,sr) match {
        case (False(), _) => True()
        case (_, True()) => True()
        case (True(), _) => sr
        case (_, False()) => Not(sl)
        case _ => Implies(sl, sr)
      }
    }
    case Not(True()) => False()
    case Not(False()) => True()
    case _ => f

  }) ensuring(_ => time <= ? *size(f) + ?)
}
