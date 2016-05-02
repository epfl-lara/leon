import leon.annotation._
import leon.lang._
import leon.collection._


object ClassToCompare {
  val listOneElement = List(1)

  val listOneElement_2 = List(2)

  def match_value(x: Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
  }





}