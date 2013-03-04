/*package leon
package smtlib

*//** AST definitions */
/*object Trees {*/
  
  /* EXPRESSIONS 
  abstract class Expr
  trait Identifier {
    def Name : String
  }
  
   Basic      
   case class Variable(i: Int) extends Expr with Identifier {
     override def Name = { "a"+i }
   }
   case class Lambda(i: Int) extends Expr with Identifier {
     override def Name = { "l"+i }
   }*/
/*   case class Literal(value: Double) extends Expr  
   case class BooleanLiteral(value: Boolean) extends Expr
    
   Propositional logic 
   case class And(exprs: Seq[Expr]) extends Expr 
   case class Or(exprs: Seq[Expr]) extends Expr   
   case class Not(expr: Expr) extends Expr
     
   Arithmetic 
  case class Plus(lhs: Expr, rhs: Expr) extends Expr 
  case class Minus(lhs: Expr, rhs: Expr) extends Expr 
  case class UMinus(expr: Expr) extends Expr 
  case class Times(lhs: Expr, rhs: Expr) extends Expr 
  //case class Division(lhs: Expr, rhs: Expr) extends Expr 
  
  case class Equals(left: Expr,right: Expr) extends Expr
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr 
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr 
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr 
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr 
}
*/