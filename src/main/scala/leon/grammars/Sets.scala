/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.Expressions._

case class Sets(maxSize: Int) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    for (setSize <- 0 to maxSize) yield {

      val tpd = TypeParameterDef(TypeParameter.fresh("T"))

      val tag = if(setSize == 0 ) {
        Tags.Constant
      } else {
        Tags.Constructor(isTerminal = false)
      }

      sGeneric(Seq(tpd), SetType(tpd.tp), Seq.fill(setSize)(tpd.tp), { subs => FiniteSet(subs.toSet, tpd.tp) }, tag)
    }
  }
}
