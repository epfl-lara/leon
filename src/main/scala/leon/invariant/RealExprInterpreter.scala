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
     val divisor = BigInt(num).gcd(BigInt(denom)).intValue
     RealLiteral(num/divisor, denom/divisor)
  }

  def plainEvaluate(expr : Expr) : (Int,Int) = expr match{
    
    case UMinus(e) => {
        val (num,denom) = plainEvaluate(e)
        (-num,denom)
    }
    case Minus(lhs,rhs) => {
        plainEvaluate(Plus(lhs,UMinus(rhs)))
    }
    case Plus(lhs,rhs) =>  {
        val (lnum,ldenom) = plainEvaluate(lhs)
	val (rnum,rdenom) = plainEvaluate(rhs)        
        ((lnum * rdenom + rnum * ldenom),(ldenom * rdenom))
    }
    case Times(lhs,rhs) =>  {
        val (lnum,ldenom) = plainEvaluate(lhs)
	val (rnum,rdenom) = plainEvaluate(rhs)
        ((lnum * rnum),(ldenom * rdenom))
    }
    case Division(lhs,rhs) => {
        val (lnum,ldenom) = plainEvaluate(lhs)
	val (rnum,rdenom) = plainEvaluate(rhs)
	plainEvaluate(Times(RealLiteral(lnum,ldenom),RealLiteral(rdenom,rnum)))
    }
    case il @ IntLiteral(v) => (v,1)
    case RealLiteral(num,denom) => (num,denom)
    case _ => throw IllegalStateException("Not a real valued expression: "+expr)
  }
}
