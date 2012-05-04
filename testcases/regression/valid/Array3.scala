object Array1 {

  def foo(): Int = {
    val a = Array.fill(5)(0)
    var i = 0
    var sum = 0
    while(i < a.length) {
      sum = sum + a(i)
      i = i + 1
    }
    sum
  } ensuring(_ == 0)

}
