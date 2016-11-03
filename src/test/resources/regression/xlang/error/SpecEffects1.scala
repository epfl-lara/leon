object SpecEffects1 {

  case class A(var x: Int)

  def update(b: A): Unit = {
    b.x = b.x + 1
  }

  def foo(a: A): Unit = {
    a.x = 10
  } ensuring(res => {
    update(a)
    a.x == 11
  })

}
