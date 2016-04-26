import leon.annotation._
import leon.lang._
import leon.collection._




object PatternMatching {
  abstract class A
  case class B(x: Int) extends A


  def class_B(x: Int): B = B(x)

  def match_value(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }

  def match_subclass(x: List[Int]): Char = x match {
    case Cons(x, xs) => 'a'
    case Nil() => 'b'
  }


}
