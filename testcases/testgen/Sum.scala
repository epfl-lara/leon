import leon.Utils._

object Sum {

  def sum(n: Int): Int = {
    waypoint(1, if(n <= 0) 0 else n + sum(n-1))
  } ensuring(_ >= 0)

}
