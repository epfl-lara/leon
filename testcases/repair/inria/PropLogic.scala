import leon.lang._
import leon.annotation._
import leon.collection._

object SemanticsPreservation { 

  sealed abstract class Formula
  case class And(lhs : Formula, rhs : Formula) extends Formula
  case class Or(lhs : Formula, rhs : Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Const(v: Boolean) extends Formula
  case class Literal(id: Int) extends Formula

  def size(f : Formula) : Int = { f match {
    case And(l,r) => 1 + size(l) + size(r)
    case Or(l,r) =>  1 + size(l) + size(r)
    case Not(e) => 1 + size(e)
    case _ => 1
  }} ensuring { _ >= 0 }

  def eval(formula: Formula)(implicit trueVars : Set[Int]): Boolean = formula match {
    case And(lhs, rhs) => eval(lhs) && eval(rhs)
    case Or(lhs, rhs)  => eval(lhs) || eval(rhs)
    case Not(f) => !eval(f)
    case Const(v) => v
    case Literal(id) => trueVars contains id
  }

  def nnf(formula : Formula) : Formula = { formula match {
    case Not(And(lhs,rhs)) => Or(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Or(lhs,rhs)) => And(nnf(Not(lhs)), nnf(Not(rhs)))
    case Not(Const(v)) => Const(!v)
    case Not(Not(e)) => nnf(e)
    case And(lhs, rhs) => And(nnf(lhs), nnf(rhs))
    case Or(lhs, rhs)  => Or(nnf(lhs), nnf(rhs))
    case other => other 
  }} ensuring { res => 
    isNNF(res)
  }

  def isNNF(f : Formula) : Boolean = f match {
    case Not(Literal(_)) => true
    case Not(_) => false
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case _ => true
  }

    
}
