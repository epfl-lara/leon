/* Copyright 2009-2016 EPFL, Lausanne */

package test

import leon.annotation._

object Print {

  // Print a 32-bit integer using the *correct*
  // format for printf in C99
  @extern
  @cCode.function(
   includes = "inttypes.h:stdio.h",
   code = """
     |void __FUNCTION__(int32_t x) {
     |  printf("%"PRIi32, x);
     |}
     """
  )
  def myprint(x: Int): Unit = {
    print(x)
  }

  @extern
  @cCode.function(
    includes = "stdio.h",
    code = """
      |void __FUNCTION__(char c) {
      |  printf("%c", c);
      |}
      """
  )
  def myprint(c: Char): Unit = {
    print(c)
  }

  @extern
  @cCode.function(
    includes = "stdio.h",
    code = """
      |void __FUNCTION__(char* s) {
      |  printf("%s", s);
      |}
      """
  )
  def myprint(s: String): Unit = {
    print(s)
  }

  def foo = myprint(58)

  def main() = {
    myprint(42)
    foo

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

