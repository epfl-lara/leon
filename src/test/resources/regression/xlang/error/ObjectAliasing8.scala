import leon.lang._

object ObjectAliasing8 {

  case class A(var x: Int)
  case class B(a1: A, a2: A)

  def updateB(b: B): Unit = {
    b.a1.x = 42
    b.a2.x = 41
  }

  def update(a: A): Unit = {
    updateB(B(a, a))
  } ensuring(_ => a.x == 42)

}
