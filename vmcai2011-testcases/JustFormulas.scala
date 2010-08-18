import scala.collection.immutable.Set

object JustFormulas {
  def vc1(x: Set[Int]) : Boolean = {
    (x.size == 0) == (x == Set.empty[Int])
  } ensuring(_ == true)
}
