import leon.Utils._

object Epsilon3 {

  def pos(): Int = {
    epsilon((y: Int) => y > 0)
  } ensuring(_ >= 0)

  def posWrong(): Int = {
    epsilon((y: Int) => y >= 0)
  } ensuring(_ > 0)

}
