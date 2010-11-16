import scala.collection.immutable.Set
import funcheck.Utils._

object ImplicationElimination { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def simplify(f: Formula): Formula = f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }

  def freeVars(f: Formula): Set[Int] = {
    require(isSimplified(f))
    f match {
      case And(lhs, rhs) => freeVars(lhs) ++ freeVars(rhs)
      case Or(lhs, rhs) => freeVars(lhs) ++ freeVars(rhs)
      case Not(f) => freeVars(f)
      case Literal(i) => Set[Int](i)
    }
  }

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }
}
