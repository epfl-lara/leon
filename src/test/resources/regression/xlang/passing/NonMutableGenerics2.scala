import leon.lang._

object NonMutableGenerics2 {

  case class C(var x: Int)

  def mut[A: Mutable](x: A): Unit = ()

  def test(): Unit = {
    val c = C(42)
    mut(c)
  }

}
