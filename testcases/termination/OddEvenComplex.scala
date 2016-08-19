/* Copyright 2009-2016 EPFL, Lausanne */

object OddEvenComplex {

  def isOdd(n: BigInt): Boolean = {
    if(n < 0) isOdd(-n)
    else if(n == 0) false
    else isEven(n-1)
  } //ensuring { res => (n % 2 == 1) == res }

  def isEven(n: BigInt): Boolean = {
    if(n < 0) isEven(-n)
    else if(n == 0) true
    else isOdd(n-1)
  } //ensuring { res => (n % 2 == 0) == res }

}