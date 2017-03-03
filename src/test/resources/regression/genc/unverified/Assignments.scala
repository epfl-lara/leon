/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation.extern

import leon.io.{ FileOutputStream => FOS }

object Assignments {

  def output(x: Int, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fos.isOpen)
    fos.write(x) && fos.write(" ")
  }

  case class Wrapper(var b: Boolean)

  def compile() = {
    implicit val state = leon.io.newState

    val fos = FOS.open("test.txt")

    val x = 42

    val abort0 = false
    val abort1 = abort0 || output(x, fos)

    var abort = false
    abort = abort || output(x, fos)

    val w = Wrapper(false)
    w.b = w.b || abort || output(x, fos)

    fos.close
  }

  def _main() = {
    compile()
    0
  }

  @extern
  def main(args: Array[String]): Unit = _main()
}

