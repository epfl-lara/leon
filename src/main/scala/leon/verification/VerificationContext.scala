/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.Program
import solvers._

case class VerificationContext (
  context: LeonContext,
  program: Program,
  solverFactory: SolverFactory[Solver],
  reporter: Reporter
)
