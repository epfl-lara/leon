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

  def hole_large_match_value(x:Int): Char = x match {
    case 1 => 'a'
    case 2 => 'b'
    case 3 => ??? [Char]
    case 4 => 'd'
  }

  def hole_encapsulated_match_value(x: Int): Char = x match {
    case x2 if x2 < 10 =>
      x2 match {
        case 1 => ??? [Char]
        case 2 => 'b'
      }
    case _ => 'z'
  }

  def hole_that_doesnt_match(x: Int, y: Int): Char ={
    if (x > y) 'x'
    else ??? [Char]
  }

  def hole_match_val(x:Int): Char = {
    val somme: Char = ??? [Char]

    if (somme == 'a') 'a' else 'b'
  }

  def hole_replace(x: BigInt, list: List[Char], char: Char): List[Char] = {
    val size = list.size
    val ret: List[Char] = if (x < 0 || x > size) {
      list
    } else {
      ??? [List[Char]]
    }
    ret
  }


}