/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Definitions.Program

// This solver utilizes the define-funs-rec command of SMTLIB-2.5 to define mutually recursive functions.
// It is not meant as an underlying solver to UnrollingSolver, and does not handle HOFs.
abstract class SMTLIBCVC4QuantifiedSolver(context: LeonContext, program: Program)
  extends SMTLIBCVC4Solver(context, program)
  with SMTLIBQuantifiedSolver
  with SMTLIBCVC4QuantifiedTarget
