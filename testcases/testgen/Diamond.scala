import leon.lang._

object Diamond {

  def foo(x: Int): Int = waypoint(1, if(x < 0) bar(x) else bar(x))

  def bar(y: Int): Int = if(y > 5) y else -y

}
