import leon.lang._
import leon.collection._
import leon._

object test {
  
  def universalEquality(e1: BigInt, e2: BigInt): Boolean = {
    val b = proveEquality(e1, e2)
    e1 == e2
  }.holds
  
  def proveEquality(a: BigInt, b: BigInt): Boolean = {
    proveEquality(a, b)
  } ensuring { res => res == (a == b) && res }

}
