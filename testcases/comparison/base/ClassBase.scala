import leon.annotation._
import leon.lang._
import leon.collection._


object ClassBase {
  val listOneElement = List(1)

  def match_value(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }

  def encapsulated_match_value(x: Int): Char = x match {
    case x2 if x2 < 10 =>
      x2 match {
        case 1 => 'a'
        case 2 => 'b'
      }
    case _ => 'z'
  }

  def inversed_match_value(x: Int): Char = x match {
    case 2 => 'b'
    case 1 => 'a'
  }




}