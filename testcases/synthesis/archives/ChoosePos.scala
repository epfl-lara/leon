import leon.lang._
import leon.lang.synthesis._

object ChoosePos {

  def c1(x: BigInt): BigInt =  choose { (y: BigInt) => y > x }

}
