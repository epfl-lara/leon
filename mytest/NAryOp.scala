object NAryOp {

  def foo(): Int = ({

    var a = 2
    bar({a = a + 1; a}, {a = 5 - a; a}, {a = a + 2; a})
  }) ensuring(_ == 9)


  def bar(i1: Int, i2: Int, i3: Int): Int = i1 + i2 + i3

}
