import leon.annotation._

object Prime {
  // an attempt at defining isPrime in PureScala...

  // for positive numbers only
  def isPrime(i : BigInt) : Boolean = {
    (i >= 2 && noneDivides(2, i))
  }

  def noneDivides(start : BigInt, number : BigInt) : Boolean = {
    if(start == number) {
      true
    } else {
      !divides(start, number) && noneDivides(start + 1, number)
    }
  }

  // for positive numbers only
  def divides(i : BigInt, j : BigInt) : Boolean = {
    val result = i == j || (i < j && ((j / i) * i == j))
    result
  }

  // no a problem
  def allTheseArePrime() : Boolean = {
    isPrime(2) && isPrime(31) && isPrime(2) && isPrime(17) && isPrime(53)
  } ensuring(res => res)

  // Can't seem to get that one to work in reasonable time
  //  def findTwoLargePrimes(x : BigInt, y : BigInt) : Boolean = {
  //    x > 200 && y > x && isPrime(x) && isPrime(y)
  //  } ensuring(res => !res)

  // Seems to work with lucky tests only :)
  def findLargePrime(x : BigInt) : Boolean = {
    x > 200 && isPrime(x)
  } ensuring(res => !res)

  // Just for testing.
  @ignore
  def main(args : Array[String]) : Unit = {
    def test(n : BigInt) : Unit = {
      println("Is " + n + " prime ? -> " + isPrime(n))
    }
    test(119)
    test(31)
    test(1)
    test(2)
    test(0)

    println(allTheseArePrime)
  }
}
