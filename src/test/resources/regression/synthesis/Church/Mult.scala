/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.lang.synthesis._

object ChurchNumerals {
  sealed abstract class Num
  case object Z extends Num
  case class  S(pred: Num) extends Num

  def value(n:Num) : Int = {
    n match {
      case Z => 0
      case S(p) => 1 + value(p)
    }
  } ensuring (_ >= 0)

  def add(x : Num, y : Num) : Num = (x match {
    case Z => y
    case S(p) => add(p, S(y))
  }) ensuring (value(_) == value(x) + value(y))

  //def distinct(x : Num, y : Num) : Num = (x match {
  //  case Z =>
  //    S(y)

  //  case S(p) =>
  //    y match {
  //      case Z =>
  //        S(x)
  //      case S(p) =>
  //        Z
  //    }
  //}) ensuring (res => res != x  && res != y)

  def mult(x: Num, y: Num): Num = {
    choose { (r : Num) =>
      value(r) == value(x) * value(y)
    }
  }
}
