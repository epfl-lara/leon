/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Definitions.Program

import theories._

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
 */
class SMTLIBZ3QuantifiedSolver(context: SolverContext, program: Program)
  extends SMTLIBZ3Solver(context, program)
     with SMTLIBQuantifiedSolver
     with SMTLIBZ3QuantifiedTarget
