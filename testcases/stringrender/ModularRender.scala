/** 
  * Name:     ModularRender.scala
  * Creation: 26.01.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Modular rendering, in one order or the other.
  */
import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object ModularRender {
  def customToString[T](l : List[T], f : (T) => String): String =  {
    ???
  } ensuring {
    (res : String) => (l, res) passes {
      case Nil() =>
        "[]"
      case Cons(t, Nil()) =>
        "[" + f(t) + "]"
      case Cons(ta, Cons(tb, Nil())) =>
        "[" + f(ta) + ", " + f(tb) + "]"
      case Cons(ta, Cons(tb, Cons(tc, Nil()))) =>
        "[" + f(ta) + ", " + f(tb) + ", " + f(tc) + "]"
    }
  }
  
  def booleanToString(b: Boolean) = if(!b) "Up" else "Down"
  
  case class Configuration(flags: List[Boolean])

  // We want to write Config:[Up,Down,Up....]
  def ConfigToString(config : Configuration): String = 
    ???[String] ask config
}
