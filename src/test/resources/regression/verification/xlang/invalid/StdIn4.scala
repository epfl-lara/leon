import leon.io._

object StdIn4 {

  def readBoolCanBeFalse: Boolean = {
    implicit val state = leon.io.newState
    StdIn.readBoolean
  } ensuring(res => res)

}
