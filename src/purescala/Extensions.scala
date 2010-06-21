package purescala

import purescala.Trees._
import purescala.Definitions._

object Extensions {
  sealed abstract class Extension(reporter: Reporter)

  abstract class Solver(reporter: Reporter) {
    // Returns Some(true) if valid, Some(false) if invalid,
    // None if unknown.
    def solve(expression: Expr) : Option[Boolean]
  }
  
  abstract class Analyser(reporter: Reporter) {
    // Does whatever the analysis should. Uses the reporter to
    // signal results and/or errors.
    def analyze(program: Program) : Unit
  }
}
