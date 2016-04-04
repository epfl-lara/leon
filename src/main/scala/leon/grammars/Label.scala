/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._

case class Label(tpe: TypeTree, aspects: List[Aspect] = Nil) extends Typed {
  val getType = tpe

  def asString(implicit ctx: LeonContext): String = {
    val ts = tpe.asString

    ts + aspects.map(_.asString).mkString
  }

  def withAspect(a: Aspect) = Label(tpe, aspects :+ a)
}
