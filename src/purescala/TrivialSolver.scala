package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

class TrivialSolver(reporter: Reporter) extends Solver(reporter) {
  val description = "Solver for syntactically trivial formulas"
  override val shortDescription = "trivial"

  def solve(expression: Expr) : Option[Boolean] = expression match {
    case BooleanLiteral(v) => Some(v)
    case Not(BooleanLiteral(v)) => Some(!v)
    case Or(exs) if exs.contains(BooleanLiteral(true)) => Some(true)
    case And(exs) if exs.contains(BooleanLiteral(false)) => Some(false)
    case _ => None
  }

}
