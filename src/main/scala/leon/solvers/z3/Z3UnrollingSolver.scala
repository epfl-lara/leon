/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package z3

import purescala.Definitions._

import unrolling._
import theories._

class Z3UnrollingSolver(context: SolverContext, program: Program, underlying: Z3Solver)
  extends UnrollingSolver(context, program, underlying,
                          new StringEncoder(context.context, program) >>
                          new BagEncoder(context.context, program))
     with Z3Solver
