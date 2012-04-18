object Capture {

  def foo(i: Int): Int = {
    val a = 3
    def rec(j: Int): Int = if(j == a) 0 else 1
    rec(3)
  }
}

// vim: set ts=4 sw=4 et:
