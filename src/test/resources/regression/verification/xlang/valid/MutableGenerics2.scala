import leon.lang._

object MutableGenerics2 {

  case class C(var x: Int)

  def hofImplicit[A: Mutable](f: (Int, A) => Int, a: A)(implicit c: C): Int = f(1, a)

  //shouldn't be able to instantiate with mutable type
  def test(): Int = {
    implicit val c = C(12)
    val state = C(42)
    hofImplicit((x: Int, s: C) => { s.x = s.x + 1; x }, state)
    assert(state.x == 43)
    0
  }

}
