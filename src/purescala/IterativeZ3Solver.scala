package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

class IterativeZ3Solver(reporter: Reporter) extends Z3Solver(reporter) {
  override val description = "Z3 Solver (w/ feedback loop)"
  override val shortDescription = "Z3/loop"

  override def solve(expression: Expr) : Option[Boolean] = {
    Some(false)
  }
}
