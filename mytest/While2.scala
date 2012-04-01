object While1 {

  def foo(): Int = {
    var a = 0
    var i = 0
    while({i = i+2; i <= 10}) {
      a = a + i
      i = i - 1
    }
    a
  } ensuring(_ == 54)

}

// vim: set ts=4 sw=4 et:
