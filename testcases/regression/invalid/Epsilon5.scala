import leon.Utils._

object Epsilon5 {

  def fooWrong(x: Int, y: Int): Int = {
    epsilon((z: Int) => z >= x && z <= y)
  } ensuring(_ > x)

}
