object Assign1 {

  def foo(): Int = {
    var a = 1
    var b = a
    a = a + 1
    b = b + a
    a
  }

}
