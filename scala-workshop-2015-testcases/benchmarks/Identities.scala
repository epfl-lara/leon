import leon.lang._
import leon.collection._
import leon._

object Identities {

  def identity(x: Int): Int = {
    require(x > 0)
    x / x
  } ensuring { res => res == 1 }

  def basic(x: Int): Int = {
    require(x > 0 && x < 10000)
    (2*x + x*x) / x
  } ensuring(res => res == x + 2)

  def nonLinear(x: Int): Int = {
    require(x > 0 && x < 10000)
    (x*x + x*(x + 3*x)) / x
  } ensuring { res => res == 5*x }


  def simplifyDivision(x: Int): Int = {
    require(x > 0 && x < 10000)
    (2*x*x + 4*x) / (2*x)
  } ensuring { res => res == x + 2 }

  //def simplifyDivision(x: BigInt): BigInt = {
  //  require(x > 0 && x < 10000)
  //  (2*x*x + 4*x) / (2*x)
  //} ensuring { res => res == x + 2 }

  def simplifyDivisionOverflow(x: Int): Int = {
    require(x > 0)
    (2*x*x + 4*x) / (2*x)
  } ensuring { res => res == x + 2 }

  
}
