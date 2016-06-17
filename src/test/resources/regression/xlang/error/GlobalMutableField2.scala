import leon.lang._
import leon.util.Random

object GlobalMutableField2 {

  val seed: Random.State = Random.State(0)

  val t = T(Random.nextBigInt(seed))

  case class T(n:BigInt) {
    require(n >= 0)
  }

}
