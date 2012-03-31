object Plus {

  def foo(): Int = ({

    var a = 2

    {a = a + 1; a} + {a = 5 - a; a}
  }) ensuring(_ == 5)


}
