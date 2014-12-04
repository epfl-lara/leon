/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.Definitions._
import utils.Helpers._

import utils._

case object CEGIS extends CEGISLike[TypeTree]("CEGIS") {
  def getGrammar(sctx: SynthesisContext, p: Problem) = {
    ExpressionGrammars.default(sctx, p)
  }

  def getRootLabel(tpe: TypeTree): TypeTree = tpe
}
