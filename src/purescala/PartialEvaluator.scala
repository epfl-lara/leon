package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._

class PartialEvaluator(val program: Program) {
  val reporter = Settings.reporter

  // Simplifies by partially evaluating.
  // Of course, I still have to decide what 'simplified' means.
  def apply(expression: Expr) : Expr = {
    def rec(expr: Expr, letMap: Map[Identifier,Expr]) : Expr = {
      expr
    }

    rec(expression, Map.empty)
  }
}
