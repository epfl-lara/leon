/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Definitions.Program

/**
 * This solver models function definitions as universally quantified formulas.
 * It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
 */
class SMTLIBZ3QuantifiedSolver(context: LeonContext, program: Program) extends SMTLIBZ3Solver(context, program)
  with SMTLIBQuantifiedSolver
  with SMTLIBZ3QuantifiedTarget
