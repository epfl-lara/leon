/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Common.Identifier
import leon.purescala.Expressions.{Lambda, Expr}
import solvers.Model

import scala.collection.mutable.{Map => MutableMap}

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

class GlobalContext(val model: Model, val maxSteps: Int, val check: Boolean) {
  var stepsLeft = maxSteps

  val lambdas: MutableMap[Lambda, Lambda] = MutableMap.empty
}

trait HasDefaultRecContext extends ContextualEvaluator {
  type RC = DefaultRecContext
  def initRC(mappings: Map[Identifier, Expr]) = DefaultRecContext(mappings)
}

trait HasDefaultGlobalContext extends ContextualEvaluator {
  def initGC(model: solvers.Model, check: Boolean) = new GlobalContext(model, this.maxSteps, check)
  type GC = GlobalContext
}