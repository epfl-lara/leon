/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Definitions._
import purescala.Constructors._

/** A grammar of equalities
  *
  * @param types The set of types for which equalities will be generated
  */
case object Equalities extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    val tpd = TypeParameterDef(TypeParameter.fresh("T"))

    List( sGeneric(Seq(tpd), BooleanType, Seq(tpd.tp, tpd.tp), { case List(sub1, sub2) => equality(sub1, sub2) }) )
  }
}
