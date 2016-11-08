/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object RecursiveADT2 {
  case class T(t: Option[T])

  def _main() = {
    val t = T(None[T])
    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

