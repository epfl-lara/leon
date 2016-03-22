/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object CaseClass {

  case class Color(r: Int, g: Int, b: Int)

  def red  = Color(0, 255, 0)
  def cyan = Color(0, 255, 255)

  def sub(c: Color, d: Color) = Color(c.r - d.r, c.g - d.g, c.b - d.b)

  def main = {
    val c = red
    val d = cyan
    val z = sub(c, d).g
    z
  } ensuring { _ == 0 }

}

