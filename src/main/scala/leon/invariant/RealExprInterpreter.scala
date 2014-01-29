package leon
package invariant

import purescala._
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
    plainEvaluate(expr)               
  }

  def plainEvaluate(expr: Expr): RealLiteral = expr match {

    case UMinus(e) => {
      val RealLiteral(num, denom) = plainEvaluate(e)
      RealLiteral(-num, denom)
    }
    case Minus(lhs, rhs) => {
      plainEvaluate(Plus(lhs, UMinus(rhs)))
    }
    case Plus(lhs, rhs) => {
      val RealLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RealLiteral(rnum, rdenom) = plainEvaluate(rhs)
      //TODO: consider using the lcm
      normalize(RealLiteral((lnum * rdenom + rnum * ldenom), (ldenom * rdenom)))
    }
    case Times(lhs, rhs) => {
      val RealLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RealLiteral(rnum, rdenom) = plainEvaluate(rhs)
      normalize(RealLiteral((lnum * rnum), (ldenom * rdenom)))
    }
    case Division(lhs, rhs) => {
      val RealLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RealLiteral(rnum, rdenom) = plainEvaluate(rhs)
      plainEvaluate(Times(RealLiteral(lnum, ldenom), RealLiteral(rdenom, rnum)))
    }
    case il @ IntLiteral(v) => RealLiteral(v, 1)
    case rl@RealLiteral(_, _) => normalize(rl)
    case _ => throw IllegalStateException("Not an evaluatable expression: " + expr)
  }

  def normalize(rl: RealLiteral): RealLiteral = {
    val RealLiteral(num, denom) = rl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = InvariantUtil.gcd(modNum, modDenom)
    //val divisor = BigInt(num).gcd(BigInt(denom)).intValue     
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      RealLiteral(-simpNum, -simpDenom)
    else
      RealLiteral(simpNum, simpDenom)
  }
  
  def evaluateRealPredicate(expr : Expr) : Boolean =  expr match {
    case Equals(a@RealLiteral(_,_),b@RealLiteral(_,_)) => isEQZ(evaluate(Minus(a,b)))     
    case LessEquals(a@RealLiteral(_,_),b@RealLiteral(_,_)) => isLEZ(evaluate(Minus(a,b)))
    case LessThan(a@RealLiteral(_,_),b@RealLiteral(_,_)) => isLTZ(evaluate(Minus(a,b)))
    case GreaterEquals(a@RealLiteral(_,_),b@RealLiteral(_,_)) => isGEZ(evaluate(Minus(a,b)))
    case GreaterThan(a@RealLiteral(n1,d1),b@RealLiteral(n2,d2)) => isGTZ(evaluate(Minus(a,b)))   
  }
  
  def isEQZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    if(d == 0) throw IllegalStateException("denominator zero")
    //if(d < 0) throw IllegalStateException("denominator negative: "+d)    
    (n == 0)
  }
  
  def isLEZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    if(d == 0) throw IllegalStateException("denominator zero")
    if(d < 0) throw IllegalStateException("denominator negative: "+d)    
    (n <= 0)
  }
  
  def isLTZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    if(d == 0) throw IllegalStateException("denominator zero")
    if(d < 0) throw IllegalStateException("denominator negative: "+d)    
    (n < 0)
  }
  
  def isGEZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    if(d == 0) throw IllegalStateException("denominator zero")
    if(d < 0) throw IllegalStateException("denominator negative: "+d)    
    (n >= 0)
  }
  
  def isGTZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    if(d == 0) throw IllegalStateException("denominator zero")
    if(d < 0) throw IllegalStateException("denominator negative: "+d)    
    (n > 0)
  }
  
 /* def isGEZ(rlit: RealLiteral) : Boolean = {
    val RealLiteral(n,d) = rlit  
    (n == 0) || (n > 0 && d >= 0) || (n < 0 && d < 0)
  }*/
  
  val zero = RealLiteral(0,1)
  def floor(rlit: RealLiteral): RealLiteral = {
    val RealLiteral(n,d) = rlit
    if(d == 0) throw IllegalStateException("denominator zero")
    if(d < 0) throw IllegalStateException("denominator negative: "+d)
    
    if(n == 0) zero
    else if(n > 0){
      //perform integer division      
      RealLiteral(n / d, 1)
    } else {
      //here the number is negative
      if(n % d == 0)
    	RealLiteral(n/d, 1)
      else {
        //perform integer division and subtract 1
        RealLiteral(n/d - 1, 1)
      }
    }
  }
}
