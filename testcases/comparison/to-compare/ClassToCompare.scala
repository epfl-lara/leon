import leon.annotation._
import leon.lang._
import leon.collection._
import leon.lang.synthesis._


object ClassToCompare {


  def match_value(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }

  case class B(x: Int) extends A
  abstract class A

  def class_B(x: Int): B = B(x)

  def hole_match_value(x:Int): Char = x match {
    case 1 => 'a'
    case 2 => ??? [Char]
  }


}