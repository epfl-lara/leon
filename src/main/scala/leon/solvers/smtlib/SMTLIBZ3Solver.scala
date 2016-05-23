/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Definitions.Program
import purescala.Common.Identifier
import purescala.Expressions.Expr

import _root_.smtlib.parser.Terms.{Identifier => _, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.CommandsResponses.GetModelResponseSuccess
import _root_.smtlib.theories.Core.{Equals => _, _}

import theories._

class SMTLIBZ3Solver(sctx: SolverContext, program: Program)
  extends SMTLIBSolver(sctx, program, new StringEncoder(sctx.context, program))
     with SMTLIBZ3Target
     with z3.Z3Solver
