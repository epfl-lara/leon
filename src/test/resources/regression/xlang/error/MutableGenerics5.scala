import leon.lang._

object MutableGenerics5 {

  case class C(var x: Int)

  def hof[A](f: (Int, A) => Int, a: A): Int = f(1, a)

  //shouldn't be able to instantiate with mutable type
  def test(): Int = {
    val state = C(42)
    hof((x: Int, s: C) => { s.x = s.x + 1; x }, state)
    assert(state.x == 43)
    0
  }

}
