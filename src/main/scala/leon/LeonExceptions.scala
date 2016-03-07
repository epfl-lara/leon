/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import purescala.Common.Tree

case class LeonFatalError(msg: Option[String]) extends Exception(msg.getOrElse(""))

object LeonFatalError {
  def apply(msg: String) = new LeonFatalError(Some(msg))
}

class Unsupported(t: Tree, msg: String)(implicit ctx: LeonContext)
  extends Exception(s"${t.asString}@${t.getPos} $msg")