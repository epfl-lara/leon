package multisets

import purescala.Extensions.Solver
import purescala.Reporter
import purescala.Trees._

class Main(reporter: Reporter) extends Solver(reporter) {
  val description = "Multiset Solver"
  println("called!")

  def solve(expr: Expr) : Option[Boolean] = {
    reporter.info("Don't know how to solve anything.")
    None
  }
}
