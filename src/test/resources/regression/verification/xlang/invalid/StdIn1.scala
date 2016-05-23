import leon.io._

object StdIn1 {

  def alwaysPos: Int = {
    implicit val state = StdIn.newState
    StdIn.readInt
  } ensuring(_ >= 0)

}
