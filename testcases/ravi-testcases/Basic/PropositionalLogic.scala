import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object PropositionalLogic { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  //case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula
  
  def size(f : Formula) : Int = (f match {
    case And(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Or(lhs, rhs) => size(lhs) + size(rhs) + 1
    //case Implies(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Not(f) => size(f) + 1
    case Literal(_) => 1    
  }) ensuring(res => res >=0 template((a) => a <= 0))

  /*def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
  }) ensuring(res => true template((a,b,c) => time <= a*size(f) + b))*/
  
  /*def isNNF(f: Formula): Boolean = { f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
    case _ => false
    
  }}*/ //ensuring((res) => true template((a,b) => time <= a*size(f) + b))
  
  def nnf(formula: Formula): Formula = (formula match {
    
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs) => Or(nnf(lhs), nnf(rhs))
    //case Implies(lhs, rhs) => Implies(nnf(lhs), nnf(rhs))
    case Not(And(lhs, rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
   // case Not(Or(lhs, rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
//    case Not(Implies(lhs, rhs)) => And(nnf(lhs), nnf(Not(rhs)))
    case Not(Not(f)) => nnf(f)
    case Not(Literal(_)) => formula
    case Literal(_) => formula
    case _ => formula
  }) ensuring(res => true template((a,b) => size(res) <= a*size(formula) + b))
  //ensuring(res => true template((a,b) => size(res) <= a*size(formula) + b)) 
  //ensuring(res => true template((a,b,c) => time <= a*size(formula) + b))  
  //ensuring(res => size(res) <= 2*size(formula) - 1)
}
