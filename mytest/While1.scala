object While1 {

  def foo(): Int = {
    var a = 0
    var i = 0
    while(i < 10) {
      a = a + i
      i = i + 1
    }
    a
  }

}
