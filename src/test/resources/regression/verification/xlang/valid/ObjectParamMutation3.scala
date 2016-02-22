import leon.lang._

object ObjectParamMutation3 {

  case class A() {
    var y: Int = 10
  }

  def update(a: A): Unit = {
    a.y = a.y + 3
  } ensuring(_ => a.y == old(a).y + 3)

  def f(): Int = {
    val a = A()
    update(a)
    a.y
  } ensuring(res => res == 13)

}
