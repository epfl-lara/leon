/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package z3

import purescala.Definitions._

import unrolling._
import theories._

class Z3UnrollingSolver(context: LeonContext, program: Program, underlying: Solver)
  extends UnrollingSolver(context, program, underlying, new StringEncoder(context, program) >> new BagEncoder(context, program))
