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
    ???[String] ask j
  }
}