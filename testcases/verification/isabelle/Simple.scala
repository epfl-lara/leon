import leon.annotation._
import leon.lang._

object Simple {

  val truth: Boolean = true holds
  val contradiction: Boolean = false holds

  val equality = { val x = (); val y = (); x == y } holds

  def ints(x: BigInt, y: BigInt) = {
    require { x > 0 && y > 0 }
    x + y
  } ensuring { _ > 0 }

  val chars = { val x = 'a'; val y = 'a'; x == y } holds

}
