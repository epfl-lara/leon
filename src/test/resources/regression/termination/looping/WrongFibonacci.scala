
object Test {
  
  def fib(n: BigInt): BigInt = {
    fib(n-1) + fib(n-2)
  } ensuring {res => res == (5*n + 1)*(5*n - 1)}
  
}
