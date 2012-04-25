import leon.Utils._

object Epsilon1 {

  def foo(x: Int): Int = {
    epsilon((y: Int) => y >= x)
  } ensuring(_ > x)

}
