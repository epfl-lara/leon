import leon.collection._
import leon.lang._
import leon.lang.synthesis._

object Length {

  def foo(l : List[Int]) : Int = 
    choose { res:Int => (l, res) passes {
      case Nil() => 0
      case Cons(a, Nil()) => 2
      case Cons(_, Cons(_, Cons(_, Cons(_, Nil())))) => 8
    }}

}
