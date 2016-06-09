import leon.annotation._
import leon.lang._
import leon.collection._


object ClassBase {

//
//  def match_value(x: Int): Char = x match {
//    case 1 => 'a'
//    case 2 => 'b'
//  }

  def inversed_match_value(x: Int): Char = x match {
    case 2 => 'b'
    case 1 => 'a'
  }

//
//
//  def encapsulated_match_value(x: Int): Char = x match {
//    case x2 if x2 < 10 =>
//      x2 match {
//        case 1 => 'a'
//        case 2 => 'b'
//      }
//    case _ => 'z'
//  }
//
//  def large_match_value(x:Int): Char = x match {
//    case 1 => 'a'
//    case 2 => 'b'
//    case 3 => 'c'
//    case 4 => 'd'
//  }
//
//  def tricky_for_ClassList_match_value(x:Int): Char = {
//    val somme = x match {
//      case 1 => 'a'
//      case 2 => 'c'
//    }
//
//    if (somme == 'a') 'a' else 'b'
//  }
//
//  case class B(x: Int) extends A
//  case class C(x: Int, y: Int) extends A
//  abstract class A
//
//  def class_B(x: Int): B = B(x)
//
//  def class_C(x:Int, y: Int): C = C(x, y)
//
//
//
//



}
