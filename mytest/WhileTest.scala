import leon.Utils._

object WhileTest {
//  object InvariantFunction {
//    def invariant(x: Boolean): Unit = ()
//  }
//  implicit def while2Invariant(u: Unit) = InvariantFunction
  def foo(x : Int) : Int = {
    require(x >= 0)

    var y : Int = x

    (while (y >= 0) {
      y = y - 1
      // assert(y >= -1)
    }) invariant(y >= -1)

    y + 1
  } ensuring(_ == 0)
}
