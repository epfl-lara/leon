object SpecEffects3 {

  case class A(var x: Int)

  def update(b: A): Boolean = {
    b.x = b.x + 1
    true
  }

  def foo(a: A): Unit = {
    a.x = 10
    assert(update(a))
  } ensuring(res => {
    a.x == 11
  })

}
