/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._

object Aliasing6 {

  case class Buffer(val array: Array[Int], var len: Int) {
    require(0 <= len && len <= array.length)

    def apply(i: Int): Int = {
      require(0 <= i && i < len)
      array(i)
    }

    def append(x: Int): Unit = {
      require(len < array.length)
      array(len) = x
      len += 1
    }
  }

  @inline
  def createBuffer() = Buffer(Array.fill(10)(0), 0)

  def _main(): Int = {
    val b1 = createBuffer()
    val b2 = Buffer(Array(1, 2, 3, 0, 0), 3)

    b1.append(b2(1))

    if (b1(0) == 2 && b1.len == 1) 0
    else 1
  } ensuring { _ == 0 }

  @extern
  def main(args: Array[String]): Unit = _main()
}

