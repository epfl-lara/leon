package leon
package grammars

import purescala.Types._

case class Label[T](t: TypeTree, l: T, depth: Option[Int] = None) extends Typed {
  val getType = t

  override def asString(implicit ctx: LeonContext) = t.asString+"#"+l+depth.map(d => "@"+d).getOrElse("")
}
