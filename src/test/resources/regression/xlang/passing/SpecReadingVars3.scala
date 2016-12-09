import leon.lang._

object SpecReadingVars3 {

  case class A(var x: Int)

  def foo(a: A): Unit = {
    require(a.x >= 0)

    def getX(a: A) = a.x

    def rec(): Unit = {
      require(getX(a) >= 0)
      if(a.x < 10) {
        a.x += 1
        rec()
      }
    } ensuring(_ => a.x >= 0)
    rec()

    assert(a.x >= 10)
  }

}
