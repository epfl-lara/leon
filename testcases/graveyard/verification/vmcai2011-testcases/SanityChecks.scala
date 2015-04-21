import leon.lang._

object SanityChecks {
  // These are just to provide some "uninterpreted function symbols"
  // Use the option -P:leon:tolerant to avoid warnings about it.
  def f1(x: Int) : Int =           { throw new Exception("Not implemented") }
  def f2(s: Set[Int]) : Set[Int] = { throw new Exception("Not implemented") }
  def f3(x: Int) : Set[Int] =      { throw new Exception("Not implemented") }
  def f4(s: Set[Int]) : Int =      { throw new Exception("Not implemented") }

  def vc01(x: Int, y: Int) = {
    require (x != y)
    Set(x, y)
  } ensuring {_.size == 2}

  def vc02(x: Int, y: Int) = {
    require (x == y)
    Set(x, y)
  } ensuring {_.size == 1}

  def vc03(A: Set[Int], B: Set[Int]) = {
    require(
      (A -- B).size == 0 &&
      (B -- A).size == 0
    )
    f2(A)
  } ensuring {_ == f2(B)}

  def vc04(A: Set[Int], B: Set[Int]) = {
    require(
      (A -- B).size == 0 &&
      (B -- A).size == 0
    )
    f4(A)
  } ensuring {_ == f4(B)}

  def vc05(x: Int, y: Int) = {
    require(
      (f3(x) -- f3(y)).size > 0 ||
      (f3(y) -- f3(x)).size > 0
    )
    x
  } ensuring {_ != y}

  def vc06(A: Set[Int], B: Set[Int]) = {
    require(
      (f2(A) -- f2(B)).size > 0 ||
      (f2(B) -- f2(A)).size > 0
    )
    A
  } ensuring {_ != B}

  def vc07(A: Set[Int], B: Set[Int], C: Set[Int]) = {
    require(
       A.size == 1
    && B.size == 1
    && C.size == 1
    && (C -- A).size == 0
    && (C -- B).size == 0
    )
    A ** B
  } ensuring(_.size == 1)

  def vc08(a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      a.size == 0
   && b.size == 0
    )
    f4(a) == f4(b)
  } ensuring(_ == true)

  def vc09(x: Int, a: Set[Int], b: Set[Int]) : Boolean = {
    require(
      a.size == 1
   && b.size == 1
   && a.contains(x)
   && b.contains(x)
    )
    f4(a) == f4(b)
  } ensuring(_ == true)

  def vc10_broken(a: Set[Int], b: Set[Int]) : Boolean = {
    f4(a ++ b) == f4(b ++ a)
  } ensuring(_ == true)

  def vc11_broken(a: Int, b: Int, c: Int, S: Set[Int]) : Int = {
    require (
      f1(a) != f1(b) && (b + 1) != (c + 1) && (c * 2) != (a * 2) &&
      (S contains a) && (S contains b) && (S contains c)
    )
    S.size
  } ensuring(_ > 2)
}
