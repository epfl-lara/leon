object ValSideEffect {

  def foo(): Int = ({

    var a = 2
    var a2 = 1

    val b = {a = a + 1; a2 = a2 + 1; a} + {a = 5 - a; a}
    a = a + 1
    a2 = a2 + 3
    a + a2 + b
  }) ensuring(_ == 13)


}

// vim: set ts=4 sw=4 et:
