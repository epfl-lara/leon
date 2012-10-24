import leon.Utils._

object Array4 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2)
    a(2)
  } ensuring(_ == 0)

}
