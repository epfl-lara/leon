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

class SMTLIBZ3Solver(context: LeonContext, program: Program)
  extends SMTLIBSolver(context, program, new StringEncoder)
     with SMTLIBZ3Target {

  def getProgram: Program = program
}
