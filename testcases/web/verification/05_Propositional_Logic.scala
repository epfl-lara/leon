import leon.lang._
import leon.annotation._
import leon.proof._

object PropositionalLogic {

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: BigInt) extends Formula

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }) ensuring(isSimplified(_))

  def isSimplified(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
  }

  def nnf(formula: Formula): Formula = (formula match {
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    case Implies(lhs, rhs) => nnf(Or(Not(lhs), rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
  }) ensuring(isNNF(_))

  def isNNF(f: Formula): Boolean = f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => false
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
  }

  def evalLit(id : BigInt) : Boolean = (id == 42) // could be any function
  def eval(f: Formula) : Boolean = f match {
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs) => eval(lhs) || eval(rhs)
    case Implies(lhs, rhs) => !eval(lhs) || eval(rhs)
    case Not(f) => !eval(f)
    case Literal(id) => evalLit(id)
  }

  @induct
  def simplifySemantics(f: Formula) : Boolean = {
    eval(f) == eval(simplify(f))
  } holds

  // Note that matching is exhaustive due to precondition.
  def vars(f: Formula): Set[BigInt] = {
    require(isNNF(f))
    f match {
      case And(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Or(lhs, rhs) => vars(lhs) ++ vars(rhs)
      case Not(Literal(i)) => Set[BigInt](i)
      case Literal(i) => Set[BigInt](i)
    }
  }

  def fv(f : Formula) = { vars(nnf(f)) }

  @induct
  def simplifyPreservesNNF(f: Formula) : Boolean = {
    require(isNNF(f))
    isNNF(simplify(f))
  } holds

  @induct
  def nnfIsStable(f: Formula) : Boolean = {
    require(isNNF(f))
    nnf(f) == f
  } holds

  @induct
  def simplifyIsStable(f: Formula) : Boolean = {
    require(isSimplified(f))
    simplify(f) == f
  } holds

  def and(lhs: Formula, rhs: Formula): Formula = And(lhs, rhs)
  def or(lhs: Formula, rhs: Formula): Formula = Or(lhs, rhs)
  
  def simplifyPreserveNNFNot(f: Formula): Boolean = {
    (nnf(Not(simplify(f))) == nnf(Not(f))) because {
      f match {
        case And(lhs, rhs) => {
          nnf(Not(simplify(f)))                                ==| trivial                     |
          nnf(Not(And(simplify(lhs), simplify(rhs))))          ==| trivial                     |
          or(nnf(Not(simplify(lhs))), nnf(Not(simplify(rhs)))) ==| simplifyPreserveNNFNot(lhs) |
          or(nnf(Not(lhs)), nnf(Not(simplify(rhs))))           ==| simplifyPreserveNNFNot(rhs) |
          or(nnf(Not(lhs)), nnf(Not(rhs)))                     ==| trivial                     |
          nnf(Not(And(lhs, rhs)))                              ==| trivial                     |
          nnf(Not(f))
        } qed
        case Or(lhs, rhs) => {
          nnf(Not(simplify(f)))                                 ==| trivial                     |
          nnf(Not(Or(simplify(lhs), simplify(rhs))))            ==| trivial                     |
          and(nnf(Not(simplify(lhs))), nnf(Not(simplify(rhs)))) ==| simplifyPreserveNNFNot(lhs) |
          and(nnf(Not(lhs)), nnf(Not(simplify(rhs))))           ==| simplifyPreserveNNFNot(rhs) |
          and(nnf(Not(lhs)), nnf(Not(rhs)))                     ==| trivial                     |
          nnf(Not(Or(lhs, rhs)))                                ==| trivial                     |
          nnf(Not(f))
        } qed
        case Implies(lhs, rhs) => {
          nnf(Not(simplify(f)))                                      ==| trivial                     |
          nnf(Not(Or(Not(simplify(lhs)), simplify(rhs))))            ==| trivial                     |
          and(nnf(Not(Not(simplify(lhs)))), nnf(Not(simplify(rhs)))) ==| trivial                     |
          and(nnf(simplify(lhs)), nnf(Not(simplify(rhs))))           ==| simplifyPreserveNNFNot(rhs) |
          and(nnf(simplify(lhs)), nnf(Not(rhs)))                     ==| simplifyPreserveNNF(lhs)    |
          and(nnf(lhs), nnf(Not(rhs)))                               ==| trivial                     |
          nnf(Not(Implies(lhs, rhs)))
        } qed
        case Not(g) => {
          nnf(Not(simplify(f)))      ==| trivial                |
          nnf(Not(Not(simplify(g)))) ==| trivial                |
          nnf(simplify(g))           ==| simplifyPreserveNNF(g) |
          nnf(g)                     ==| trivial                |
          nnf(Not(Not(g)))           ==| trivial                |
          nnf(Not(f))
        } qed
        case Literal(_) => trivial
      }
    }
  } holds
  
  def simplifyPreserveNNF(f: Formula): Boolean = {
    (nnf(simplify(f)) == nnf(f)) because {
      f match {
        case And(lhs, rhs) => {
          nnf(simplify(f))                            ==| trivial                  |
          and(nnf(simplify(lhs)), nnf(simplify(rhs))) ==| simplifyPreserveNNF(lhs) |
          and(nnf(lhs), nnf(simplify(rhs)))           ==| simplifyPreserveNNF(rhs) |
          and(nnf(lhs), nnf(rhs))                     ==| trivial                  |
          nnf(f)
        } qed
        case Or(lhs, rhs) => {
          nnf(simplify(f))                           ==| trivial                  |
          or(nnf(simplify(lhs)), nnf(simplify(rhs))) ==| simplifyPreserveNNF(lhs) |
          or(nnf(lhs), nnf(simplify(rhs)))           ==| simplifyPreserveNNF(rhs) |
          or(nnf(lhs), nnf(rhs))                     ==| trivial                  |
          nnf(f)
        } qed
        case Implies(lhs, rhs) => {
          nnf(simplify(f))                                ==| trivial                       |
          nnf(or(Not(simplify(lhs)), simplify(rhs)))      ==| trivial                       |
          or(nnf(Not(simplify(lhs))), nnf(simplify(rhs))) ==| simplifyPreserveNNF(rhs)      |
          or(nnf(Not(simplify(lhs))), nnf(rhs))           ==| trivial                       |
          or(nnf(simplify(Not(lhs))), nnf(rhs))           ==| simplifyPreserveNNF(Not(lhs)) |
          or(nnf(Not(lhs)), nnf(rhs))                     ==| trivial                       |
          nnf(f)
        } qed
        case Not(g) => {
          nnf(simplify(f))      ==| trivial                   |
          nnf(Not(simplify(g))) ==| simplifyPreserveNNFNot(g) |
          nnf(Not(g))           ==| trivial                   |
          nnf(f)
        } qed
        case Literal(_) => trivial
      }
    }
  } holds
}
