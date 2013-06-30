package leon
package invariant

import purescala.DataStructures._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import java.io._
import leon.Reporter

object RealValuedExprInterpreter {

  def evaluate(expr : Expr) : RealLiteral = {
     val (num,denom) = plainEvaluate(expr)
     
     //compute GCD of numerator and denomenator
     gcd(num,denom)
  }

  def plainEvaluate(expr : Expr) : (Int,Int) = expr match{
    
    case UMinus(e) => {
        val (num,denom) = evaluate(e)
        (-num,denom)
    }
    case Minus(lhs,rhs) => {
        evaluate(Plus(lhs,UMinus(rhs)))
    }
    case Plus(lhs,rhs) =>  {
        val (lnum,ldenom) = evaluate(lhs)
	val (rnum,rdenom) = evaluate(rhs)        
        ((lnum * rdenom + rnum * ldenom),(ldenom * rdenom))
    }
    case Times(lhs,rhs) =>  {
        val (lnum,ldenom) = evaluate(lhs)
	val (rnum,rdenom) = evaluate(rhs)
        ((lnum * rnum),(ldenom * rdenom))
    }
    case Division(lhs,rhs) => {
        val lval = evaluate(lhs)
	val (rnum,rdenom) = evaluate(rhs)
	Times(lval,RealLiteral(rdenom,rnum))
    }
    case il @ IntLiteral(v) => (v,1)
    case RealLiteral(num,denom) => (num,denom)
    case _ => throw NotSupportedException("Not a real valued expression: "+expr)
  }
}
