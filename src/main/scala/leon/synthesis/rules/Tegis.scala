/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Constructors._

import evaluators._
import datagen._

import utils._

case object TEGIS extends TEGISLike[TypeTree]("TEGIS") {
  def getGrammar(sctx: SynthesisContext, p: Problem) = {
    ExpressionGrammars.default(sctx, p)
  }

  def getRootLabel(tpe: TypeTree): TypeTree = tpe
}
