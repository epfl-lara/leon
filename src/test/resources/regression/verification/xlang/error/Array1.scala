object Array1 {

  def foo(): Int = {
    (Array.fill(5)(5))(2) = 3
    0
  }

}
