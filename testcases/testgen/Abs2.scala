import leon.lang._
import leon.annotation._

object Abs2 {

  @main
  def f(x: Int): Int = if(x < 0) g(-x) else g(x)

  def g(y: Int): Int = if(y < 0) -y else y

}
