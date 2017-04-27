/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object OperatorEquals7 {

  def test(a: String, b: String) = a == b

  def _main(): Int = {
    val str1 = "Hello"
    val str2 = "GenC"
    if (test(str1, str1) && test(str2, str2)) {
      if (test(str1, str2)) 1
      else 0
    } else 2
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

