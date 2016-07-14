import leon.io._

object StdIn1 {

  def abs: BigInt = {
    implicit val state = StdIn.newState
    val n = StdIn.readBigInt
    if(n < 0) -n else n
  } ensuring(_ >= 0)

}
