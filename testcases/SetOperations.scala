import scala.collection.immutable.Set

// Cardinalities not supported yet.
// Pre/Post conditions commented out.

object SetOperations {
    def add(a: Set[Int], b: Int) : Set[Int] = {
        require(a.size >= 0)
        a ++ Set(b)
      } ensuring((x:Set[Int]) => x.size >= a.size)
}
