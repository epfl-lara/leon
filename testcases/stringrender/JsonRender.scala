/** 
  * Name:     JsonRender.scala
  * Creation: 25.11.2015
  * Author:   Mikael Mayer (mikael.mayer@epfl.ch)
  * Comments: Json specifications
  */

import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object JsonRender {
  abstract class JValue
  abstract class JCompositeValue extends JValue
  abstract class JFinalValue extends JValue
  case class JDict(values: List[(String, JValue)]) extends JCompositeValue
  case class JArray(values: List[JValue]) extends JCompositeValue
  case class JString(value: String) extends JFinalValue
  case class JBoolean(value: Boolean) extends JFinalValue
  case class JInt(value: Int) extends JFinalValue
  
  def json_render(j: JValue): String = {
    ???[String]
  } ensuring( (res: String) => (j, res) passes {
      case JString("foo") => "\"foo\""
      case JBoolean(true) => "true"
      case JInt(10) => "10"
      case JArray(Cons(JInt(10), Cons(JInt(21), Nil()))) => "[10, 21]"
      /*case JDict(Cons(("confid", JInt(10)), Cons(("paper", JDict(Cons(("strings", JInt(20)), Cons(("integers", JInt(32)), Nil())))), Nil()))) =>
"""{
  "confid": 10,
  "paper": {
    "strings": 20,
    "integers": 32
  }
}
"""*/
    }
  )
}