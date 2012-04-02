object Match {

  sealed abstract class A
  case class B(b: Int) extends A
  case class C(c: Int) extends A

  def foo(a: A): Int = ({

    var i = 0
    var j = 0

    {i = i + 1; a} match {
      case B(b) => {i = i + 1; b}
      case C(c) => {j = j + 1; i = i + 1; c}
    }
    i
  }) ensuring(_ == 2)
}
