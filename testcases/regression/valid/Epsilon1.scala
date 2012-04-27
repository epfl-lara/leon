import leon.Utils._

object Epsilon1 {

  def greater(x: Int): Int = {
    epsilon((y: Int) => y > x)
  } ensuring(_ >= x)

}
