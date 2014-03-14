/* Copyright 2009-2014 EPFL, Lausanne */

object Fibonacci {
  def fib(x: Int) : Int = {
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
}
