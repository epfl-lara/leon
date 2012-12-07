object Prog001 {
  def fortyTwo() = 42

  def plus(x : Int, y : Int) = x + y

  def double(x : Int) : Int = {
    val a = x
    a + a
  }

  def implies(a : Boolean, b : Boolean) : Boolean = !a || b

  def abs(x : Int) : Int = {
    if(x < 0) -x else x
  }

  def factorial(i : Int) : Int = if(i <= 1) 1 else (i * factorial(i - 1))
}
