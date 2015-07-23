object Fibonacci {

  def fib(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x < 2) {
      x
    } else {
      fib(x - 1) + fib(x - 2)
    }
  }

  // requires that fib is universally quantified to work...
  def check() : Boolean = {
    fib(5) == 5
  } ensuring(_ == true)


  def f(n : BigInt) : BigInt = {
    require(n >= 0)
    if(n <= 0)
      BigInt(1)
    else
      f(n-1) + g(n-1)
  }

  def g(n : BigInt) : BigInt = {
    require(n >= 0)
    if(n <= 0)
      BigInt(1)
    else
      f(n-1) 
  } ensuring(_ == fib(n + 1))

}
