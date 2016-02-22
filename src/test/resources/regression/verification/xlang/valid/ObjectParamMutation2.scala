import leon.lang._

object ObjectParamMutation2 {

  case class A() {
    var y: Int = 10
  }

  def update(a: A): Unit = {
    a.y = 12
  } ensuring(_ => a.y == 12)

  def f(): Int = {
    val a = A()
    update(a)
    a.y
  } ensuring(res => res == 12)

}
