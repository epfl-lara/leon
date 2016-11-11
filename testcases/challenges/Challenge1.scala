
object Test3 {

  case class A(var x: Int) {
    require(x > 0)
  }

  def foo(as: Array[A]): Int = {
    require(as.length > 1)
    as(1).x
  } ensuring(_ > 0)

}
