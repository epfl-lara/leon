/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object CaseClass {

  case class Color(r: Int, g: Int, b: Int) {
    def getR = r
  }

  def green = Color(0, 255, 0)
  def cyan  = Color(0, 255, 255)

  def sub(c: Color, d: Color) = Color(c.r - d.r, c.g - d.g, c.b - d.b)

  def main = {
    val c = green
    val d = cyan
    val z = sub(c, d).g

    if (c.getR == 0) z
    else -1
  } ensuring { _ == 0 }

}

