/* Copyright 2009-2016 EPFL, Lausanne */

package test

import leon.annotation._

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


  def main() = {
    myprint(42)

    // Testing escaped characters support
    myprint('\n')
    myprint('\t')
    myprint('\"')
    myprint('\\')
    myprint('\'')
    myprint("\"ab'&\n\t\\\\")
    myprint('\n')

    0
  }
}

