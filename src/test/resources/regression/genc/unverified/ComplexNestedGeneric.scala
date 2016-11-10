/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object ComplexNestedGeneric {

  def _main() = {
    def foo[A](opt: Option[A]) = {
      var local: Option[A] = None[A]

      def inner(b: Boolean) {
        if (b) local = Some(opt.get)
      }

      inner(opt.isDefined)

      local.isDefined
    }

    if (foo(None[Int]) == false && foo(Some(true)) == true) 0
    else 1
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

