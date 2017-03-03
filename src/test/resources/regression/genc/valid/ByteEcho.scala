/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.io._

object ByteEcho {

  def _main(): Int = {
    implicit val state = newState

    var b = StdIn.tryReadByte()

    while (b.isDefined) {
      StdOut.print(b.get)
      b = StdIn.tryReadByte()
    }

    0
  }

  @extern
  def main(args: Array[String]) = _main()

}

