/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.io.{ FileOutputStream => FOS, FileInputStream => FIS }
import leon.io.{ StdIn, StdOut }

object IO {

  def getFileName() = "test.txt"

  def printX(x: Int, c: Char, sep: String): Unit = {
    val filename = getFileName
    val out = FOS.open(filename)
    if (out.isOpen) {
      out.write(x)
      out.write(sep)
      out.write(c)
      out.close
    } else {
      StdOut.print("CANNOT PRINT ")
      StdOut.print(x)
      StdOut.print(sep)
      StdOut.print(c)
      StdOut.print(" TO FILE ")
      StdOut.print(filename)
      StdOut.print("\n")
    }
  }

  def echo(): Unit = {
    implicit val state = leon.io.newState
    StdOut.print("ECHOING...")
    val x = StdIn.readInt
    StdOut.print(x)
    StdOut.print("\n")
  }

  def slowEcho(): Unit = {
    implicit val state = leon.io.newState

    val message = 58

    val out = FOS.open("echo.txt")
    if (out.isOpen) {
      out.write(message)
      out.close

      ()
    } else {
      StdOut.print("Couldn't write message\n")
    }

    val in = FIS.open("echo.txt")
    if (in.isOpen) {
      val x = in.readInt
      in.close

      if (x == message) {
        StdOut.print("The echo was slow but successful!\n")
      } else
        StdOut.print("The echo was slow and buggy! :-(\n")
    } else {
      StdOut.print("Couldn't read message\n")
    }
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
    slowEcho()

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

