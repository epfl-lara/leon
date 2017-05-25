/* Copyright 2009-2016 EPFL, Lausanne */

package leon.lang
import leon.annotation._
import scala.Boolean
import scala.Predef.???

@ignore
class Real {

   def +(a: Real): Real = ???
   def -(a: Real): Real = ???
   def *(a: Real): Real = ???
   def /(a: Real): Real = ???

   def unary_- : Real = ???

   def > (a: Real): Boolean = ???
   def >=(a: Real): Boolean = ???
   def < (a: Real): Boolean = ???
   def <=(a: Real): Boolean = ???

}

@ignore
object Real {
  def apply(n: scala.math.BigInt, d: scala.math.BigInt): Real = ???
  def apply(n: scala.math.BigInt): Real = ???
}
