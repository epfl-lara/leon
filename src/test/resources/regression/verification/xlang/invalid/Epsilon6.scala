import leon.Utils._

object Epsilon6 {

  def greaterWrong(x: Int): Int = {
    epsilon((y: Int) => y >= x)
  } ensuring(_ > x)

}
