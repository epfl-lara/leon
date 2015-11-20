/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common.Identifier
import purescala.Expressions.Expr
import solvers.Model

trait RecContext[RC <: RecContext[RC]] {
  def mappings: Map[Identifier, Expr]

  def newVars(news: Map[Identifier, Expr]): RC

  def withNewVar(id: Identifier, v: Expr): RC = {
    newVars(mappings + (id -> v))
  }

  def withNewVars(news: Map[Identifier, Expr]): RC = {
    newVars(mappings ++ news)
  }
}

case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext[DefaultRecContext] {
  def newVars(news: Map[Identifier, Expr]) = copy(news)
}

class GlobalContext(val model: Model, val maxSteps: Int) {
  var stepsLeft = maxSteps
}

protected[evaluators] trait DefaultContexts extends ContextualEvaluator {

  final type RC = DefaultRecContext
  final type GC = GlobalContext

  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
  def initGC(model: solvers.Model) = new GlobalContext(model, this.maxSteps)
}