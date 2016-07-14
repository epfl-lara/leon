import leon.io._

object StdIn2 {

  def anyTwoNumbers: Boolean = {
    implicit val state = StdIn.newState
    val n1 = StdIn.readInt
    val n2 = StdIn.readInt

    n1 == n2
  } ensuring(res => res)

}
