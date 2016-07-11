import leon.io._

object StdIn1 {

  def alwaysPos: Int = {
    implicit val state = leon.io.newState
    StdIn.readInt
  } ensuring(_ >= 0)

}
