/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

object NonIntegralMain {

  def _main() = {
    val a = "Hello, World!"
    a
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

