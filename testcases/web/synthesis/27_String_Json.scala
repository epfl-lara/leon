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
  abstract class JSON
  abstract class JCompositeValue extends JSON
  abstract class JFinalValue extends JSON
  case class JDict(values: Map[String, JSON]) extends JCompositeValue
  case class JArray(values: List[JSON]) extends JCompositeValue
  case class JString(value: String) extends JFinalValue
  case class JBoolean(value: Boolean) extends JFinalValue
  case class JInt(value: Int) extends JFinalValue
  
  def JStringToString(j: JString) = "\"" + StrOps.escape(j.value) + "\""
  
  def test = json_render(JDict(Map("title" -> JString("\"test\""), "flags" -> JArray(List(JInt(1), JBoolean(true))))))
 
  /** Synthesize this function by example to have a JSON serializer. */
  def json_render(j: JSON): String = ???[String]
}