/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.io.{ FileOutputStream => FOS }
import leon.io.{ StdIn, StdOut }

object Print {

  def getFileName() = "test.txt"

  def printX(x: Int, c: Char, sep: String): Unit = {
    val filename = getFileName
    val out = FOS.open(filename)
    if (out.isOpen) {
      out.write(x)
      out.write(sep)
      out.write(c)
      out.close()
    } else {
      StdOut.print("CANNOT PRINT ")
      StdOut.print(x)
      StdOut.print(sep)
      StdOut.print(c)
      StdOut.print(" TO FILE ")
      StdOut.print(filename)
    }
  }

  def echo(): Unit = {
    implicit val state = leon.io.newState
    StdOut.print("ECHOING...")
    val x = StdIn.readInt
    StdOut.print(x)
  }

  def _main() = {
    StdOut.print(42)

    // Testing escaped characters support
    StdOut.print('\n')
    StdOut.print('\t')
    StdOut.print('\"')
    StdOut.print('\\')
    StdOut.print('\'')
    StdOut.print("\"ab'&\n\t\\\\")
    StdOut.print('\n')

    printX(42, '*', " <--> ")

    echo()

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

