package orderedsets

import purescala.Reporter
import purescala.Extensions._
import purescala.Trees._

class Main(reporter: Reporter) extends Solver(reporter) {
  val description = "Solver for constraints on ordered sets"

  def solve(expr: Expr) : Option[Boolean] = {
    reporter.info(expr, "I have no idea how to solve this :(")
    None
  }
}
