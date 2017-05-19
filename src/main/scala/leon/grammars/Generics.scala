/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Definitions.Program
import purescala.Expressions.GenericValue

/** Generate GenericValues for all type parameters in the progra*/
case class Generics(prog: Program) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    val tpds =
      prog.definedClasses.flatMap(_.tparams) ++
      prog.definedFunctions.flatMap(_.tparams)

    for {
      tpd <- tpds
      i   <- Seq(1, 2, 3)
      tp = tpd.tp
    } yield {
      sTerminal(tp, GenericValue(tp ,i))
    }
  }
}
