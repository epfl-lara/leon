
object Test {

  def isOdd(n: BigInt): Boolean = {
    isEven(n-1)
  } ensuring { res => (n % 2 == 1) == res }
  
  def isEven(n: BigInt): Boolean = {
    isOdd(n-1)
  } ensuring { res => (n % 2 == 0) == res }
  
  
}