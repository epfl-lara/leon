import leon.lang._

object ExpressionOrder {
  case class Pixel(rgb: Int)
  case class Matrix(data: Array[Int], w: Int, h: Int)

  def fun = 0xffffff
  def foo = 4
  def bar(i: Int) = i * 2
  def baz(i: Int, j: Int) = bar(i) - bar(j)

  def syntaxCheck {
    val p = Pixel(fun)
    val m = Matrix(Array(0, 1, 2, 3), 2, 2)

    val z = baz(foo, bar(foo))
    val a = Array(0, 1, foo / 2, 3, bar(2), z / 1)

    val t = (true, foo, bar(a(0)))
  }

  def main =
      bool2int(test0(false), 1)  +
      bool2int(test1(42),    2)  +
      bool2int(test2(58),    4)  +
      bool2int(test3(false), 8)  +
      bool2int(test4(false), 16) +
      bool2int(test6,        32) +
      bool2int(test7,        64)

  def test0(b: Boolean) = {
    val f = b && !b // == false

    var c = 0

    val x = f && { c = 1; true }

    c == 0
  }

  def test1(i: Int) = {
    require(i > 0)

    val j = i / i * 3 // == 3

    var c = 0
    val x = { c = c + 3; j } + { c = c + 1; j } * { c = c * 2; j }

    c == 8 && j == 3 && x == 12
  }

  def test2(i: Int) = {
    var c = 0;
    val x = if (i < 0) { c = 1; -i } else { c = 2; i }

    if (i < 0) c == 1
    else c == 2
  }

  def test3(b: Boolean) = {
    val f = b && !b // == false

    var c = 0
    val x = f || { c = 1; true } || { c = 2; false }

    c == 1
  }

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
  }

  def test5(b: Boolean) = {
    val f = b && !b // == false

    var c = if (f) 0 else -1

    c = c + (if (f) 0 else 1)

    c == 0
  }

  def test6 = {
    val a = Array(0, 1, 2, 3, 4)
    def rec(b: Boolean, i: Int): Boolean = {
      if (a.length <= i + 1) b
      else rec(if (a(i) < a(i + 1)) b else false, i + 1)
    }

    rec(true, 0)
  }

  def test7 = {
    var c = 1

    val a = Array(0, 1, 2, 3, 4)

    a(if(a(0) == 0) { c = c + 1; 0 } else { c = c + 2; 1 }) = { c = c * 2; -1 }

    c == 4
  }

  def bool2int(b: Boolean, f: Int) = if (b) 0 else f;
}


