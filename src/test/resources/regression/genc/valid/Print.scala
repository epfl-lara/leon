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
    println(x)
  }

  def foo = myprint(58)

  def main() = {
    myprint(42)
    foo
    0
  }
}

