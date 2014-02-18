/* Copyright 2009-2013 EPFL, Lausanne */

package leon

case class LeonFatalError(msg: Option[String]) extends Exception(msg.getOrElse(""))

object LeonFatalError {
  def apply(msg: String) = new LeonFatalError(Some(msg))
}
