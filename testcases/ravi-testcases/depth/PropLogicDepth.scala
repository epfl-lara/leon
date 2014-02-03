import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object PropLogicDepth { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula
  
  def max(x: Int,y: Int) = if (x >= y) x else y
  
  def nestingDepth(f: Formula) : Int = (f match {
    case And(lhs, rhs) => max(nestingDepth(lhs),nestingDepth(rhs)) + 1
    case Or(lhs, rhs) => max(nestingDepth(lhs),nestingDepth(rhs)) + 1
    case Implies(lhs, rhs) => max(nestingDepth(lhs),nestingDepth(rhs)) + 1
    case Not(f) => nestingDepth(f) + 1
    case Literal(_) => 1    
  })  

  def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case Literal(_) => f
    
  }) ensuring((res) => true template((a,b) => depth <= a*nestingDepth(f) + b))

  def isSimplified(f: Formula): Boolean = {f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
    
  }} ensuring((res) => true template((a,b) => depth <= a*nestingDepth(f) + b))

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
  }) ensuring((res) => true template((a,b) => depth <= a*nestingDepth(formula) + b))

  def isNNF(f: Formula): Boolean = { f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
    case _ => false
    
  }} ensuring((res) => true template((a,b) => depth <= a*nestingDepth(f) + b))
}