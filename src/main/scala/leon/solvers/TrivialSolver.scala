/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

class TrivialSolver(context: LeonContext) extends Solver(context) with NaiveIncrementalSolver {
  val name = "trivial"
  val description = "Solver for syntactically trivial formulas"

  def solve(expression: Expr) : Option[Boolean] = expression match {
    case BooleanLiteral(v) => Some(v)
    case Not(BooleanLiteral(v)) => Some(!v)
    case Or(exs) if exs.contains(BooleanLiteral(true)) => Some(true)
    case And(exs) if exs.contains(BooleanLiteral(false)) => Some(false)
    case Equals(l,r) if l == r => Some(true)
    case _ => None
  }
}
