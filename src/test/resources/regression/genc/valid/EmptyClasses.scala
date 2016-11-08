/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern
import leon.lang._

object EmptyClasses {
  // For most of the following classes, GenC will emit warnings and a byte field will be added

  case class Empty()

  case class Full(e: Empty)

  sealed abstract class Units()
  case class Kg() extends Units
  case class Lb() extends Units

  sealed abstract class Option
  case class None() extends Option
  case class Some(x: Int) extends Option

  def bar() = Empty()

  def testIf(b: Boolean) = if (b) Empty() else bar()

  def testOption(b: Boolean) = if (b) None() else Some(42)

  def testUnits(b: Boolean) = if (b) Kg() else Lb()

  // Compilation only
  def _main() = {
    val empty1 = Empty()
    val empty2 = Empty()

    val empty3 = bar()

    val empty4 = testIf(true)
    val empty5 = testIf(false)

    val full1 = Full(Empty())
    val full2 = Full(bar())
    val full3 = Full(empty1)

    val none = None()
    val some = Some(58)
    val option1 = testOption(true)
    val option2 = testOption(false)

    val kg = Kg()
    val lb = Lb()

    val kg2 = testUnits(true)
    val lb2 = testUnits(false)

    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

