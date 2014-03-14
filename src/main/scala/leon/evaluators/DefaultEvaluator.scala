/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._

class DefaultEvaluator(ctx: LeonContext, prog: Program) extends RecursiveEvaluator(ctx, prog) {
  type RC = DefaultRecContext
  type GC = GlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC = new GlobalContext(stepsLeft = 50000)

  case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext {
    def withNewVar(id: Identifier, v: Expr) = copy(mappings + (id -> v))

    def withVars(news: Map[Identifier, Expr]) = copy(news)
  }
}
