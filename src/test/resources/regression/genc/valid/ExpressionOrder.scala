/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object ExpressionOrder {
  case class Pixel(rgb: Int)
  case class Matrix(data: Array[Int], w: Int, h: Int)

  def void = ()

  def fun = 0xffffff
  def foo = 4
  def bar(i: Int) = i * 2
  def baz(i: Int, j: Int) = bar(i) - bar(j)

  def syntaxCheck(i: Int) {
    val p = Pixel(fun)
    val m = Matrix(Array(0, 1, 2, 3), 2, 2)

    val z = baz(foo, bar(foo))
    val a = Array(0, 1, foo / 2, 3, bar(2), z / 1)

    val t = (true, foo, bar(a(0)))

    val a2 = Array.fill(4)(2)
    val a3 = Array.fill(if (i <= 0) 1 else i)(bar(i))
    val b = Array(1, 2, 0)
    b(1) = if (bar(b(1)) % 2 == 0) 42 else 58

    def f1 = (if (i < 0) a else b)(0)
    def f2 = (if (i < 0) a else b).length

    //def f3 = (if (i < 0) a else b)(0) = 0 // <- not supported

    val c = (0, true, 2)
    val d = (if (i > 0) i else -i, false, 0)

    def f4 = (if (i < 0) d else c)._2 // expression result unused
  }

  def main = {
      bool2int(test0(false), 1)  +
      bool2int(test1(42),    2)  +
      bool2int(test2(58),    4)  +
      bool2int(test3(false), 8)  +
      bool2int(test4(false), 16) +
      bool2int(test6,        32) +
      bool2int(test7,        64) +
      bool2int(test8,        128)
  } ensuring { _ == 0 }

  def test0(b: Boolean) = {
    val f = b && !b // == false

    var c = 0

    val x = f && { c = 1; true }

    c == 0
  }.holds

  def test1(i: Int) = {
    require(i > 0)

    val j = i / i * 3 // == 3

    var c = 0
    val x = { c = c + 3; j } + { c = c + 1; j } * { c = c * 2; j }

    c == 8 && j == 3 && x == 12
  }.holds

  def test2(i: Int) = {
    var c = 0;
    val x = if (i < 0) { c = 1; -i } else { c = 2; i }

    if (i < 0) c == 1
    else c == 2
  }.holds

  def test3(b: Boolean) = {
    val f = b && !b // == false

    var c = 0
    val x = f || { c = 1; true } || { c = 2; false }

    c == 1
  }.holds

  def test4(b: Boolean) = {
    var i = 10
    var c = 0

    val f = b && !b // == false
    val t = b || !b // == true

    // The following condition is executed 11 times,
    // and only during the last execution is the last
    // operand evaluated
    while ({ c = c + 1; t } && i > 0 || { c = c * 2; f }) {
      i = i - 1
    }

    i == 0 && c == 22
  }.holds

  def test5(b: Boolean) = {
    val f = b && !b // == false

    var c = if (f) 0 else -1

    c = c + (if (f) 0 else 1)

    c == 0
  }.holds

  def test6 = {
    val a = Array(0, 1, 2, 3, 4)

    def rec(b: Boolean, i: Int): Boolean = {
      require(i >= 0 && i < 2147483647) // 2^31 - 1

      if (i + 1 < a.length) rec(if (a(i) < a(i + 1)) b else false, i + 1)
      else b
    }

    rec(true, 0)
  }.holds

  def test7 = {
    var c = 1

    val a = Array(0, 1, 2, 3, 4)

    a(if(a(0) == 0) { c = c + 1; 0 } else { c = c + 2; 1 }) = { c = c * 2; -1 }

    c == 4
  }.holds

  def test8 = {
    var x = 0

    def bar(y: Int) = {
      def fun(z: Int) = 1 * x * (y + z)

      fun(3)
    }

    bar(2) == 0
  }.holds

  def bool2int(b: Boolean, f: Int) = if (b) 0 else f;
}


