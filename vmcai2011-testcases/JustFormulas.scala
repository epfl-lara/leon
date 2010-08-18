import scala.collection.immutable.Set

object JustFormulas {
  def vc1(x: Set[Int]) : Boolean = {
    (x.size == 0) == (x == Set.empty[Int])
  } ensuring(_ == true)

  def vc2(x: Set[Int], y: Set[Int]) : Boolean = {
    (x == y) == (x -- y == Set.empty[Int] && y -- x == Set.empty[Int])
  } ensuring(_ == true)
}
