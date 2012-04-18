object Plus {

  def foo(): Int = ({

    var a = 2
    var b = 1

    a = {b = b + 2; a = a + 1; a} + {a = 5 - a; a}
    a + b
  }) ensuring(_ == 8)


}
