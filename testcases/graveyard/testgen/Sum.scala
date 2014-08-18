import leon.lang._
import leon.annotation._

object Sum {

  @main
  def sum(n: Int): Int = {
    if(n <= 0) waypoint(4, 0) else waypoint(3, waypoint(2, n + sum(n-1)))
  } ensuring(_ >= 0)

}
