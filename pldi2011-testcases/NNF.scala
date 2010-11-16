import scala.collection.immutable.Set
import funcheck.Utils._

object NNF { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def nnf(formula: Formula): Formula = formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
  }

  def freeVars(f: Formula): Set[Int] = {
    require(isNNF(f))
    f match {
      case And(lhs, rhs) => freeVars(lhs) ++ freeVars(rhs)
      case Or(lhs, rhs) => freeVars(lhs) ++ freeVars(rhs)
      case Not(Literal(i)) => Set[Int](i)
      case Literal(i) => Set[Int](i)
    }
  }

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }
}
