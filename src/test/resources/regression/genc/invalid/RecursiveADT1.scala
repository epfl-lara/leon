/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object RecursiveADT1 {
  sealed abstract class Expr

  case class Add(e1: Expr, e2: Expr) extends Expr
  case class Val(x: Int) extends Expr

  def eval(e: Expr): Int = e match {
    case Val(x) => x
    case Add(e1, e2) => eval(e1) + eval(e2)
  }

  def example = eval(Add(Val(42), Val(58)))

  def _main() = {
    example
    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

