import scala.collection.immutable.Set

object JustFormulas {
  def vc1(x: Set[Int]) : Boolean = {
    (x.size == 0) == (x == Set.empty[Int])
  } ensuring(_ == true)

  def vc2(x: Set[Int], y: Set[Int]) : Boolean = {
    (x == y) == (x -- y == Set.empty[Int] && y -- x == Set.empty[Int])
  } ensuring(_ == true)

  def vc3(x: Set[Int], y: Set[Int]) : Boolean = {
    (x ++ y).size > x.size + y.size - (x ** y).size
  } ensuring(_ == true)

  // def vc3(x: Set[Int], y: Set[Int], z: Set[Int]) : Boolean = {
  //   (x ++ y ++ z).size == x.size + y.size + z.size + (x ** y ** z).size - (x ** y).size - (x ** z).size - (y ** z).size
  // } ensuring(_ == true)
}
