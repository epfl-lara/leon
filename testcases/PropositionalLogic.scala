import scala.collection.immutable.Set
import leon.lang._
import leon.annotation._

object PropositionalLogic {

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula

  def size(f : Formula) : Int = (f match {
    case And(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Or(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Implies(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Not(f) => size(f) + 1
    case _ => 1
  })

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case _ => f

  })


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
    case _ => formula
  }) ensuring((res) => size(res) <= 2*size(formula) - 1)

  def nnfSimplify(f: Formula): Formula = {
     simplify(nnf(f))
  } //ensuring((res) => size(res) <= 2*size(f) - 1)

//  def vars(f: Formula): Set[Int] = {
//    require(isNNF(f))
//    f match {
//      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
//      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
//      case Implies(lhs, rhs) => vars(lhs) ++ vars(rhs)
//      case Not(Literal(i)) => Set[Int](i)
//      case Literal(i) => Set[Int](i)
//    }
//  }
}
