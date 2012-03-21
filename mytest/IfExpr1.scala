object IfExpr1 {

  def foo(): Int = {
    var a = 1
    var b = 2
    if(a == b)
      a = a + 3
    else
      b = a + b
    a
  }

}
