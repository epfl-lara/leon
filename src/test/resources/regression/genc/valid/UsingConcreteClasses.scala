/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._

object UsingConcreteClasses {

  abstract class Parent
  case class Child(opt: Some[Int]) extends Parent

  def _main() = {
    val child = Child(Some(42))

    if (child.opt.v == 42) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()

}

