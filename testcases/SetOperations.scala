import scala.collection.immutable.Set

// Cardinalities not supported yet.
// Pre/Post conditions commented out.

object SetOperations {
  def add(a: Set[Int], b: Int): Set[Int] = {
    require(a.size >= 0)
    a ++ Set(b)
  } ensuring ((x: Set[Int]) => x.size >= a.size)

  def vennRegions(a: Set[Int], b: Set[Int], c: Set[Int]) = {
    a ++ b ++ c
  } ensuring {
    _.size ==
            a.size + b.size + c.size -
            (a ** b).size - (b ** c).size - (c ** a).size +
            (a ** b ** c).size
  }

}
