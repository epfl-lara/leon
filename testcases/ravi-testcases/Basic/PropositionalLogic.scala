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

  def size(f : Formula) : Int = (f match {
    case And(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Or(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Implies(lhs, rhs) => size(lhs) + size(rhs) + 1
    case Not(f) => size(f) + 1
    case _ => 1    
  }) 

  /*def simplify(f: Formula): Formula = (f match {
    case And(lhs, rhs) => And(simplify(lhs), simplify(rhs))
    case Or(lhs, rhs) => Or(simplify(lhs), simplify(rhs))
    case Implies(lhs, rhs) => Or(Not(simplify(lhs)), simplify(rhs))
    case Not(f) => Not(simplify(f))
    case _ => f
    
  })*/ 


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

  /*def nnfSimplify(f: Formula): Formula = { 
	 simplify(nnf(f)) 
  }*/ //ensuring((res) => size(res) <= 2*size(f) - 1)

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
    
  }) ensuring((res) => true template((a,b) => time <= a*size(f) + b))

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
