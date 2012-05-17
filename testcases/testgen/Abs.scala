import leon.Utils._

object Abs {

  def abs(x: Int): Int = {
    waypoint(1, if(x < 0) -x else x) 
  } ensuring(_ >= 0)

}
