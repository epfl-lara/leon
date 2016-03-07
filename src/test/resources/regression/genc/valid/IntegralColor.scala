/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object IntegralColor {

  def isValidComponent(x: Int) = x >= 0 && x <= 255

  def getRed(rgb: Int): Int = {
    (rgb & 0x00FF0000) >> 16
  } ensuring isValidComponent _

  def getGreen(rgb: Int): Int = {
    (rgb & 0x0000FF00) >> 8
  } ensuring isValidComponent _

  def getBlue(rgb: Int): Int = {
    rgb & 0x000000FF
  } ensuring isValidComponent _

  def getGray(rgb: Int): Int = {
    (getRed(rgb) + getGreen(rgb) + getBlue(rgb)) / 3
  } ensuring isValidComponent _

  def testColorSinglePixel: Boolean = {
    val color = 0x20C0FF

    32 == getRed(color) && 192 == getGreen(color) &&
    255 == getBlue(color) && 159 == getGray(color)
  }.holds

  case class Color(r: Int, g: Int, b: Int)

  def getColor(rgb: Int) = Color(getRed(rgb), getGreen(rgb), getBlue(rgb))

  /*
   *case class Image(width: Int, height: Int, buffer: Array[Int]) {
   *  // currently not enforced:
   *  require(width <= 1000 && height <= 1000 && buffer.length == width * height)
   *}
   */

  def matches(value: Array[Int], expected: Array[Int]): Boolean = {
    require(value.length == expected.length)

    var test = true
    var idx = 0
    (while (idx < value.length) {
      test = test && value(idx) == expected(idx)
      idx = idx + 1
    }) invariant { idx >= 0 && idx <= value.length }

    test
  }

  def testColorWholeImage: Boolean = {
    val WIDTH  = 2
    val HEIGHT = 2

    /*
     *val source   = Image(WIDTH, HEIGHT, Array(0x20c0ff, 0x123456, 0xffffff, 0x000000))
     *val expected = Image(WIDTH, HEIGHT, Array(159, 52, 255, 0)) // gray convertion
     *val gray     = Image(WIDTH, HEIGHT, Array.fill(4)(0))
     */

    val source   = Array(0x20c0ff, 0x123456, 0xffffff, 0x000000)
    val expected = Array(159, 52, 255, 0) // gray convertion
    val gray     = Array.fill(4)(0)

    // NOTE: Cannot define a toGray function as XLang doesn't allow mutating
    // arguments and GenC doesn't allow returning arrays

    var idx = 0
    (while (idx < WIDTH * HEIGHT) {
      gray(idx) = getGray(source(idx))
      idx = idx + 1
    }) invariant { idx >= 0 && idx <= WIDTH * HEIGHT && gray.length == WIDTH * HEIGHT }
    // NB: the last invariant is very important -- without it the verification times out

    matches(gray, expected)
  }.holds

  // Only for square kernels
  case class Kernel(size: Int, buffer: Array[Int])

  def isKernelValid(kernel: Kernel): Boolean =
    kernel.size > 0 && kernel.size < 1000 && kernel.size % 2 == 1 &&
    kernel.buffer.length == kernel.size * kernel.size

  def applyFilter(gray: Array[Int], size: Int, idx: Int, kernel: Kernel): Int = {
    require(size > 0 && size < 1000 &&
            gray.length == size * size &&
            idx >= 0 && idx < gray.length &&
            isKernelValid(kernel))

    def up(x: Int): Int = {
      if (x < 0) 0 else x
    } ensuring { _ >= 0 }

    def down(x: Int): Int = {
      if (x >= size) size - 1 else x
    } ensuring { _ < size }

    def fix(x: Int): Int = {
      down(up(x))
    } ensuring { res => res >= 0 && res < size }

    def at(row: Int, col: Int): Int = {
      val r = fix(row)
      val c = fix(col)

      gray(r * size + c)
    }

    val mid = kernel.size / 2

    val i = idx / size
    val j = idx % size

    var res = 0
    var p = -mid
    (while (p <= mid) {
      var q = -mid

      (while (q <= mid) {
        val krow = p + mid
        val kcol = q + mid

        assert(krow >= 0 && krow < kernel.size)
        assert(kcol >= 0 && kcol < kernel.size)

        val kidx = krow * kernel.size + kcol

        res += at(i + p, j + q) * kernel.buffer(kidx)

        q = q + 1
      }) invariant { q >= -mid && q <= mid + 1 }

      p = p + 1
    }) invariant { p >= -mid && p <= mid + 1 }

    res
  }

  def testFilterConvolutionSmooth: Boolean = {
    val gray = Array(127, 255, 51, 0)
    val expected = Array(124, 158, 76, 73)
    val size = 2 // grey is size x size

    // NOTE: Cannot define a `smoothed` function as XLang doesn't allow mutating
    // arguments and GenC doesn't allow returning arrays

    val kernel = Kernel(3, Array(1, 1, 1,
                                 1, 2, 1,
                                 1, 1, 1))

    val smoothed = Array.fill(gray.length)(0)
    assert(smoothed.length == expected.length)

    var idx = 0;
    (while (idx < smoothed.length) {
      smoothed(idx) = applyFilter(gray, size, idx, kernel) / 10
      idx = idx + 1
    }) invariant { idx >= 0 && idx <= smoothed.length && smoothed.length == gray.length }

    matches(smoothed, expected)
  }.holds


  def main: Int = {
    if (testColorSinglePixel && testColorWholeImage && testFilterConvolutionSmooth) 0
    else 1
  } ensuring { _ == 0 }

}


