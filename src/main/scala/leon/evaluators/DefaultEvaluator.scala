/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Quantification._

class DefaultEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog, 50000) {
  type RC = DefaultRecContext
  type GC = GlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC(model: solvers.Model) = new GlobalContext(model)

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def newVars(news: Map[Identifier, Expr]) = copy(news)
  }
}
