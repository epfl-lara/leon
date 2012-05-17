import leon.Utils._

object MultiCall {


  def a(i: Int): Int = waypoint(1, if(i < 0) b(i) else c(i))

  def b(j: Int): Int = if(j == -5) d(j) else e(j)
  def c(k: Int): Int = if(k == 5) d(k) else e(k)

  def d(l: Int): Int = l
  def e(m: Int): Int = m

}
