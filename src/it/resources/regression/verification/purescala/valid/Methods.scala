import leon.lang._

object Methods {
  abstract class A

  abstract class B extends A {
    def foo(i: BigInt) = {
      require(i > 0)
      i + 1
    } ensuring ( _ >= 0 )
  }
  
  case class C(x: BigInt) extends B {
    val y = BigInt(42)
    override def foo(i: BigInt) = {
      x + y + (if (i>0) i else -i)
    } ensuring ( _ >= x )
  }

  case class E() extends B

  case class D() extends A

  def f1 = {
    val c = C(42)
    (if (c.foo(0) + c.x > 0) c else D()).isInstanceOf[B]
  }.holds

}
