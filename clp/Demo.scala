object Demo {
  def f(x: Int) : Boolean = {
    x > 4
  } ensuring(x => x)
}
