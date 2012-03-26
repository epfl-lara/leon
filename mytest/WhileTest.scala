object WhileTest {
  def foo(x : Int) : Int = {
    require(x >= 0)

    var y : Int = x

    while(y >= 0) {
      y = y - 1
      // assert(y >= -1)
    }

    y + 1
  } ensuring(_ == 0)
}
