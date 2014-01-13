package leon
package solvers.combinators

import purescala.Trees._
import purescala.TreeOps._
import purescala.Common._
import purescala.Definitions._

import solvers._

class SimpleTemplateFactory(cond: Expr) extends TemplateFactory[Expr] {
  val precondition = cond
  val evaluator = None

  def decode(id: Expr): Identifier = id.asInstanceOf[Variable].id

  protected def encode0(id: Identifier): Variable = Variable(id)

  protected def translate0(expr: Expr, subst: Map[Identifier,Expr]): Expr = replaceFromIDs(subst, expr)

  def replacer(idSubstMap: Map[Expr,Expr]): (Expr) => Expr = {
    (expr: Expr) => replace(idSubstMap, expr)
  }
}


// vim: set ts=4 sw=4 et:
