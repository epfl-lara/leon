/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._

object StdOut {

  @extern
  @library
  @cCode.function(
    code = """
      |void __FUNCTION__(char* s) {
      |  printf("%s", s);
      |}
      """,
    includes = "stdio.h"
  )  
  def print(x: String): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(s: String): Unit = {
    print(s)
    print('\n')
  }

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(int32_t x) {
     |  printf("%"PRIi32, x);
     |}
     """,
    includes = "inttypes.h:stdio.h"
  )  
  def print(x: Int): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(x: Int): Unit = {
    print(x)
    print('\n')
  }

  @library
  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(char c) {
      |  printf("%c", c);
      |}
      """,
    includes = "stdio.h"
  )
  def print(c: Char): Unit = {
    scala.Predef.print(c)
  }

  @library
  def println(c: Char): Unit = {
    print(c)
    print('\n')
  }

  @library
  def println(): Unit = {
    print('\n')
  }

}

