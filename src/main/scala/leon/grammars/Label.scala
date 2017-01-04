/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._

import scala.collection.immutable.TreeMap

case class Label(tpe: TypeTree, aspectsMap: TreeMap[AspectKind, Aspect] = TreeMap()) extends Typed {
  val getType = tpe

  def asString(implicit ctx: LeonContext): String = {
    val ts = tpe.asString

    ts + aspects.map(_.asString).mkString
  }

  def withAspect(a: Aspect) = {
    Label(tpe, aspectsMap + (a.kind -> a))
  }

  def aspects: Traversable[Aspect] = aspectsMap.map(_._2)
}
