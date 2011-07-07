import cp.Definitions._
import cp.Terms._

@spec object Specs {
  def isPrime(i : Int) : Boolean = {
    (i >= 2 && noneDivides(2, i))
  }

  def noneDivides(start : Int, number : Int) : Boolean = {
    if(start == number) {
      true
    } else {
      !divides(start, number) && noneDivides(start + 1, number)
    }
  }

  def divides(i : Int, j : Int) : Boolean = (i == j || (i < j && ((j / i) * i == j)))
}

object Primes {
  import Specs.isPrime

  // Three different ways of getting the results of the example in the CADE tool demo.
  def main(args : Array[String]) : Unit = {
    val seq1 = (
      for(
        x <- 1 to 40;
        y <- (x+1) to ((40 - 2*x)/3);
        if(isPrime(y) && ((3 * y * y) % x) == 0)) yield(x, y, (3*y*y)/x)
      ).toList

    println(seq1)

    val seq2 = (
      for(
        (x,y) <- ((x:Int, y:Int) => x > 0 && y > x && 2*x + 3*y <= 40).findAll;
        if(isPrime(y));
        z <- ((z:Int) => z * x == 3 * y * y).findAll) yield(x, y, z)
      ).toList

    println(seq2)

    val seq3 = (
      for(
        (x,y,z) <- ((x:Int, y:Int, z:Int) => x > 0 && y > x && 2*x + 3*y <= 40 && isPrime(y) && z * x == 3 * y * y).findAll) yield(x, y, z)
      ).toList

    println(seq3)
    
  }
}
