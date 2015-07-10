package leon.lang
import leon.annotation._

@ignore
class Real {

   def +(a: Real): Real = ???
   def -(a: Real): Real = ???
   def *(a: Real): Real = ???
   def /(a: Real): Real = ???

   def unary_- : Real = ???
}

object Real {
  def apply(n: BigInt, d: BigInt): Real = ???
}
