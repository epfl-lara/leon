/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.io.{ FileOutputStream => FOS }
import leon.io.StdIn

object Print {

  // Print a 32-bit integer using the *correct*
  // format for printf in C99
  @extern
  @cCode.function(
   code = """
     |void __FUNCTION__(int32_t x) {
     |  printf("%"PRIi32, x);
     |}
     """,
    includes = "inttypes.h:stdio.h"
  )
  def myprint(x: Int): Unit = {
    print(x)
  }

  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(char c) {
      |  printf("%c", c);
      |}
      """,
    includes = "stdio.h"
  )
  def myprint(c: Char): Unit = {
    print(c)
  }

  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(char* s) {
      |  printf("%s", s);
      |}
      """,
    includes = "stdio.h"
  )
  def myprint(s: String): Unit = {
    print(s)
  }

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
      myprint("CANNOT PRINT ")
      myprint(x)
      myprint(sep)
      myprint(c)
      myprint(" TO FILE ")
      myprint(filename)
    }
  }

  def echo(): Unit = {
    implicit val state = StdIn.newState
    myprint("ECHOING...")
    val x = StdIn.readInt
    myprint(x)
  }

  def _main() = {
    myprint(42)

    // Testing escaped characters support
    myprint('\n')
    myprint('\t')
    myprint('\"')
    myprint('\\')
    myprint('\'')
    myprint("\"ab'&\n\t\\\\")
    myprint('\n')

    printX(42, '*', " <--> ")

    echo()

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

