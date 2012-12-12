object Array10 {

  def foo(): Int = {
    val a = Array.fill(5)(0)
    def rec(): Array[Int] = {
      a
    }
    val b = rec()
    b(0)
  }

}
