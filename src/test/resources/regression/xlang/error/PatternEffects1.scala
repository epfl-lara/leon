object PatternEffects1 {

  case class A(var x: Int)

  def update(b: A): Boolean = {
    b.x = b.x + 1
    b.x > 0
  }

  def foo(a: A): Int = (a match {
    case A(_) if update(a) => a.x
    case _ => 10
  }) ensuring(res => res > 0)

}
