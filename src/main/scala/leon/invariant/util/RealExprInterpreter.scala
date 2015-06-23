package leon
package invariant.util

import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._

object RealValuedExprInterpreter {

  def evaluate(expr : Expr) : RationalLiteral = {
    plainEvaluate(expr)
  }

  def plainEvaluate(expr: Expr): RationalLiteral = expr match {

    case UMinus(e) => {
      val RationalLiteral(num, denom) = plainEvaluate(e)
      RationalLiteral(-num, denom)
    }
    case Minus(lhs, rhs) => {
      plainEvaluate(Plus(lhs, UMinus(rhs)))
    }
    case Plus(lhs, rhs) => {
      val RationalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RationalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      //TODO: consider using the lcm
      normalize(RationalLiteral((lnum * rdenom + rnum * ldenom), (ldenom * rdenom)))
    }
    case Times(lhs, rhs) => {
      val RationalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RationalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      normalize(RationalLiteral((lnum * rnum), (ldenom * rdenom)))
    }
    case Division(lhs, rhs) => {
      val RationalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val RationalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      plainEvaluate(Times(RationalLiteral(lnum, ldenom), RationalLiteral(rdenom, rnum)))
    }
    case il @ InfiniteIntegerLiteral(v) => RationalLiteral(v, 1)
    case rl@RationalLiteral(_, _) => normalize(rl)
    case _ => throw new IllegalStateException("Not an evaluatable expression: " + expr)
  }

  def normalize(rl: RationalLiteral): RationalLiteral = {
    val RationalLiteral(num, denom) = rl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = modNum.gcd(modDenom)
    //val divisor = BigInt(num).gcd(BigInt(denom)).intValue
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      RationalLiteral(-simpNum, -simpDenom)
    else
      RationalLiteral(simpNum, simpDenom)
  }

  def evaluateRealPredicate(expr : Expr) : Boolean =  expr match {
    case Equals(a@RationalLiteral(_,_),b@RationalLiteral(_,_)) => isEQZ(evaluate(Minus(a,b)))
    case LessEquals(a@RationalLiteral(_,_),b@RationalLiteral(_,_)) => isLEZ(evaluate(Minus(a,b)))
    case LessThan(a@RationalLiteral(_,_),b@RationalLiteral(_,_)) => isLTZ(evaluate(Minus(a,b)))
    case GreaterEquals(a@RationalLiteral(_,_),b@RationalLiteral(_,_)) => isGEZ(evaluate(Minus(a,b)))
    case GreaterThan(a@RationalLiteral(n1,d1),b@RationalLiteral(n2,d2)) => isGTZ(evaluate(Minus(a,b)))
  }

  def isEQZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    //if(d < 0) throw new IllegalStateException("denominator negative: "+d)
    (n == 0)
  }

  def isLEZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    if(d < 0) throw new IllegalStateException("denominator negative: "+d)
    (n <= 0)
  }

  def isLTZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    if(d < 0) throw new IllegalStateException("denominator negative: "+d)
    (n < 0)
  }

  def isGEZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    if(d < 0) throw new IllegalStateException("denominator negative: "+d)
    (n >= 0)
  }

  def isGTZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    if(d < 0) throw new IllegalStateException("denominator negative: "+d)
    (n > 0)
  }

 /* def isGEZ(rlit: RationalLiteral) : Boolean = {
    val RationalLiteral(n,d) = rlit
    (n == 0) || (n > 0 && d >= 0) || (n < 0 && d < 0)
  }*/

  val zero = RationalLiteral(0,1)
  def floor(rlit: RationalLiteral): RationalLiteral = {
    val RationalLiteral(n,d) = rlit
    if(d == 0) throw new IllegalStateException("denominator zero")
    if(d < 0) throw new IllegalStateException("denominator negative: "+d)

    if(n == 0) zero
    else if(n > 0){
      //perform integer division
      RationalLiteral(n / d, 1)
    } else {
      //here the number is negative
      if(n % d == 0)
    	RationalLiteral(n/d, 1)
      else {
        //perform integer division and subtract 1
        RationalLiteral(n/d - 1, 1)
      }
    }
  }
}
