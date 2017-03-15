/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import leon.purescala.Common.FreshIdentifier
import leon.purescala.Definitions.ValDef
import purescala.Types._
import purescala.Definitions._
import purescala.Expressions._

case class Tuples(maxSize: Int) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    for (tupleSize <- 2 to maxSize) yield {

      val tpds = for (i <- 1 to tupleSize) yield TypeParameterDef(TypeParameter.fresh("T"+i))
      val tps  = tpds.map(_.tp)

      sGeneric(tpds, TupleType(tps), tps, Tuple(_), Tags.Constructor(isTerminal = false))
    }
  }
}
