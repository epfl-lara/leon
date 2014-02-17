import scala.collection.immutable.Set
import leon.Utils._
import leon.Annotations._

object PropositionalLogic { 

  sealed abstract class Formula
  case class And(lhs: Formula, rhs: Formula) extends Formula
  case class Or(lhs: Formula, rhs: Formula) extends Formula
  case class Implies(lhs: Formula, rhs: Formula) extends Formula
  case class Not(f: Formula) extends Formula
  case class Literal(id: Int) extends Formula
  
  case class Pair(f: Formula, b: Boolean)
  
  sealed abstract class List
  case class Cons(x: Pair, xs: List) extends List
  case class Nil() extends List

  def size(f : Formula) : Int = (f match {
    case And(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Or(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Implies(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Not(f) => size(f) + 1
    case Literal(_) => 1    
  }) 
  
  def listSize(l: List) : Int = (l match {
    case Cons(_, xs) => 1 + listSize(xs)
    case Nil() => 0
  })

  def removeImplies(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(removeImplies(lhs), removeImplies(rhs))
    case Or(lhs, rhs) => Or(removeImplies(lhs), removeImplies(rhs))
    case Implies(lhs, rhs) => Or(Not(removeImplies(lhs)),removeImplies(rhs))
    case Not(f) => Not(removeImplies(f))
    case Literal(_) => f
    
  }) ensuring((res) => true template((a,b) => time <= a*size(f) + b))

  def isSimplified(f: Formula): Boolean = {f match {
    case And(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Or(lhs, rhs) => isSimplified(lhs) && isSimplified(rhs)
    case Implies(_,_) => false
    case Not(f) => isSimplified(f)
    case Literal(_) => true
    
  }} ensuring((res) => true template((a,b) => time <= a*size(f) + b))

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
  }) ensuring((res) => true template((a,b) => time <= a*size(formula) + b))

  def isNNF(f: Formula): Boolean = { f match {
    case And(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Or(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Implies(lhs, rhs) => isNNF(lhs) && isNNF(rhs)
    case Not(Literal(_)) => true
    case Not(_) => false
    case Literal(_) => true
    case _ => false
    
  }} ensuring((res) => true template((a,b) => time <= a*size(f) + b))

/*  def value(lit: Formula, model: List) : Boolean = (model match {
    case Cons(x,xs) => if(x.f == lit) x.b else value(lit, xs)
    case Nil() => false    
  }) ensuring(res => true template((a,b) => depth <= a*listSize(model) + b))
   
  
  def evaluate(f: Formula, model: List): Boolean = (f match {
    case And(lhs, rhs) => evaluate(lhs, model) && evaluate(rhs, model)
    case Or(lhs, rhs) => evaluate(lhs, model) || evaluate(rhs, model)
    case Implies(lhs, rhs) => (!evaluate(lhs, model)) || evaluate(rhs, model)
    case Not(f) => !evaluate(f, model)
    case Literal(_) => value(f, model)
    case _ => false
  }) ensuring((res) => true template((a,b) => depth <= a*(size(f)*listSize(model)) + b))*/
}
