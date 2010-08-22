import scala.collection.immutable.Set

object SanityChecks {
  
  // These are just to provide some "uninterpreted function symbols"
  // Use the option -P:funcheck:tolerant to avoid warnings about it.
  def f1(x: Int) : Int =           { throw new Exception("Not implemented") }
  def f2(s: Set[Int]) : Set[Int] = { throw new Exception("Not implemented") }
  def f3(x: Int) : Set[Int] =      { throw new Exception("Not implemented") }
  def f4(s: Set[Int]) : Int =      { throw new Exception("Not implemented") }


  def vc1(x: Int, y: Int) = {
    require (x != y)
    Set(x, y)
  } ensuring {_.size == 2}

  def vc2(x: Int, y: Int) = {
    require (x == y)
    Set(x, y)
  } ensuring {_.size == 1}

  def vc3(A: Set[Int], B: Set[Int]) = {
    require(
      (A -- B).size == 0 &&
      (B -- A).size == 0
    )
    f2(A)
  } ensuring {_ == f2(B)}

  def vc4(A: Set[Int], B: Set[Int]) = {
    require(
      (A -- B).size == 0 &&
      (B -- A).size == 0
    )
    f4(A)
  } ensuring {_ == f4(B)}

  def vc5(x: Int, y: Int) = {
    require(
      (f3(x) -- f3(y)).size > 0 ||
      (f3(y) -- f3(x)).size > 0
    )
    x
  } ensuring {_ != y}

  def vc6(A: Set[Int], B: Set[Int]) = {
    require(
      (f2(A) -- f2(B)).size > 0 ||
      (f2(B) -- f2(A)).size > 0
    )
    A
  } ensuring {_ != B}

}