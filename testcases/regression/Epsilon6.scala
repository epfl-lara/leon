import leon.Utils._

object Epsilon6 {

  def fooWrong(): Int = {
    epsilon((y: Int) => y > epsilon((z: Int) => z < y))
  } ensuring(_ >= 0)

  def foo(): Int = {
    epsilon((y: Int) => y > epsilon((z: Int) => z < y))
  } ensuring(res => res >= 0 || res < 0)

}
