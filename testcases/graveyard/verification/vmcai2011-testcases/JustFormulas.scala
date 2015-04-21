import leon.lang._

object JustFormulas {
  // These are just to provide some "uninterpreted function symbols"
  // Use the option -P:leon:tolerant to avoid warnings about it.
  def f1(x: Int) : Int =           { throw new Exception("Not implemented") }
  def f2(s: Set[Int]) : Set[Int] = { throw new Exception("Not implemented") }
  def f3(x: Int) : Set[Int] =      { throw new Exception("Not implemented") }
  def f4(s: Set[Int]) : Int =      { throw new Exception("Not implemented") }

  def vc1_V(x: Set[Int]) : Boolean = {
    (x.size == 0) == (x == Set.empty[Int])
  } ensuring(_ == true)

  def vc2_V(x: Set[Int], y: Set[Int]) : Boolean = {
    (x == y) == (x -- y == Set.empty[Int] && y -- x == Set.empty[Int])
  } ensuring(_ == true)

  def vc3_I(x: Set[Int], y: Set[Int]) : Boolean = {
    (x ++ y).size > x.size + y.size - (x ** y).size
  } ensuring(_ == true)

  def vc4_V(x: Set[Int], y: Set[Int], z: Set[Int]) : Boolean = {
     (x ++ y ++ z).size == x.size + y.size + z.size + (x ** y ** z).size - (x ** y).size - (x ** z).size - (y ** z).size
  } ensuring(_ == true)

  def vc5_V(x: Int, y: Int, a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      a.contains(f1(x))
   && b.contains(f1(y))
   && x < y + 1
   && 2*y - 1 < 2*x
    )
    (a ++ b).size == a.size + b.size
  } ensuring(!_)

  def vc6_V(x: Int, y: Int, a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      (!((a -- b).size == 0 && (b -- a).size == 0) || a == b)
   && f2(a).contains(x)
   && f2(b).contains(y)
   && (a -- b) == Set.empty[Int]
   && (b -- a) == Set.empty[Int]
   && f2(b).size < 2
    )
    x != y
  } ensuring(!_)

  def vc7_I(a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      a == Set(1, 2, 3)
   && (b subsetOf a)
    )
    a.contains(b.size)
  } ensuring(_ == true)

  def vc8_V(a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      a == Set(1, 2, 3)
   && (b subsetOf a)
   && b != Set.empty[Int]
    )
    a.contains(b.size)
  } ensuring(_ == true)
}
