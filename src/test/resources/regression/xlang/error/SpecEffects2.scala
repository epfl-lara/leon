object SpecEffects2 {

  case class A(var x: Int)

  def update(b: A): Unit = {
    b.x = b.x + 1
  }

  def foo(a: A): Unit = {
    require({ update(a); a.x == 10})
    a.x = a.x + 1
  } ensuring(res => {
    a.x == 11
  })

}
