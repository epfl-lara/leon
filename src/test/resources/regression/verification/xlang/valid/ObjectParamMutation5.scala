import leon.lang._

object ObjectParamMutation5 {

  case class A() {
    var x: Int = 10
    var y: Int = 13
  }

  def swap(a: A): Unit = {
    val tmp = a.x
    a.x = a.y
    a.y = tmp
  } ensuring(_ => a.x == old(a).y && a.y == old(a).x)

  def f(): A = {
    val a = A()
    swap(a)
    a
  } ensuring(res => res.x == 13 && res.y == 10)

}
