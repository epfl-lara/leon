object Array4 {

  def foo(a: Array[Int]): Int = {
    a(2)
  } ensuring(_ == 3)

}
