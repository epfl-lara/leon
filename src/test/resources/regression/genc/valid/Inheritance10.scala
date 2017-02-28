/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object Inheritance10 {

  sealed abstract class Status
  case class Success()     extends Status
  case class OpenError()   extends Status
  case class EncodeError() extends Status
  case class DecodeError() extends Status

  def statusCode(s: Status): Int = s match {
    case Success()     => 0
    case OpenError()   => 1
    case EncodeError() => 2
    case DecodeError() => 3
  }

  def _main(): Int = {
    statusCode(Success())
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

