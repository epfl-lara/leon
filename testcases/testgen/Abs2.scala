import leon.Utils._
import leon.Annotations._

object Abs2 {

  @main
  def f(x: Int): Int = if(x < 0) g(-x) else g(x)

  def g(y: Int): Int = if(y < 0) -y else y

}
