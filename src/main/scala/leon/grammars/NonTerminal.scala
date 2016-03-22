/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._

/** A basic non-terminal symbol of a grammar.
  *
  * @param t The type of which expressions will be generated
  * @param l A label that characterizes this [[NonTerminal]]
  * @param depth The optional depth within the syntax tree where this [[NonTerminal]] is.
  * @tparam L The type of label for this NonTerminal.
  */
case class NonTerminal[L](t: TypeTree, l: L, depth: Option[Int] = None) extends Typed {
  val getType = t

  override def asString(implicit ctx: LeonContext) = t.asString+"#"+l+depth.map(d => "@"+d).getOrElse("")
}
