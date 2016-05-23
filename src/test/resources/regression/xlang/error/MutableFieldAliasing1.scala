import leon.lang._

object MutableFieldAliasing1 {
  
  case class A(var x: Int)
  case class B(a: A)

  def f1(): Int = {
    val b1 = B(A(10))
    val b2 = b1
    b2.a.x = 15
    b1.a.x
  } ensuring(_ == 15)


  def build(x: Int): B = {
    val a = A(x)
    B(a)
  }

}

