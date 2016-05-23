/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Definitions.Program

// This solver utilizes the define-funs-rec command of SMTLIB-2.5 to define mutually recursive functions.
// It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
abstract class SMTLIBCVC4QuantifiedSolver(context: SolverContext, program: Program)
  extends SMTLIBCVC4Solver(context, program)
  with SMTLIBQuantifiedSolver
  with SMTLIBCVC4QuantifiedTarget
