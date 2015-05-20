import leon.lang._
import leon.annotation._

object SemanticsPreservation { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Variable(id: Int) extends Formula

  @induct
  def nnf(formula: Formula): Formula = (formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case n @ Not(_) => n
    case v @ Variable(_) => v
  }) ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(_) => false
    case Variable(_) => true
  }

  @induct
  def eval(formula: Formula): Boolean = (formula match {
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs) => eval(lhs) || eval(rhs)
    case Not(f) => !eval(f)
    case Variable(id) => id > 42
  }) ensuring(res => res == eval(nnf(formula)))

  @induct
  def nnfPreservesSemantics(f: Formula): Boolean = {
    eval(f) == eval(nnf(f))
  } holds

}
