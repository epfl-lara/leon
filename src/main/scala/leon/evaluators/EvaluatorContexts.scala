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
    if(!purescala.ExprOps.isValue(v)) {
      println(s"Trying to add $id -> $v in context butnot a value")
      println(Thread.currentThread().getStackTrace.map(_.toString).mkString("\n"))
      System.exit(0)
    }
    newVars(mappings + (id -> v))
  }

  def withNewVars(news: Map[Identifier, Expr]): RC = {
    if(news.exists{ case (k, v) => !purescala.ExprOps.isValue(v) }) {
      println(s"Trying to add $news in context but not a value")
      println(Thread.currentThread().getStackTrace.map(_.toString).mkString("\n"))
      System.exit(0)
    }
    newVars(mappings ++ news)
  }
}

case class DefaultRecContext(mappings: Map[Identifier, Expr]) extends RecContext[DefaultRecContext] {
  def newVars(news: Map[Identifier, Expr]) = copy(news)
  
  mappings.find{ case (k, v) => !purescala.ExprOps.isValue(v) } match {
    case None =>
    case Some(a) =>
    println(s"Trying to add $mappings in context but $a has not a value as second argument (of type ${a._2.getType}) and class ${a._2.getClass} because ${purescala.ExprOps.msgs}")
    println(Thread.currentThread().getStackTrace.map(_.toString).mkString("\n"))
    System.exit(0)
  }
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