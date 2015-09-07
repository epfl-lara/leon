/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Definitions.Program
import purescala.Common.Identifier
import purescala.Expressions.Expr

import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.Commands.{FunDef => SMTFunDef, _}
import _root_.smtlib.parser.CommandsResponses.GetModelResponseSuccess
import _root_.smtlib.theories.Core.{Equals => SMTEquals, _}

class SMTLIBZ3Solver(context: LeonContext, program: Program) extends SMTLIBSolver(context, program) with SMTLIBZ3Target {

  // EK: We use get-model instead in order to extract models for arrays
  override def getModel: Model = {

    val res = emit(GetModel())

    val smodel: Seq[SExpr] = res match {
      case GetModelResponseSuccess(model) => model
      case _ => Nil
    }

    var modelFunDefs = Map[SSymbol, DefineFun]()

    // First pass to gather functions (arrays defs)
    for (me <- smodel) me match {
      case me @ DefineFun(SMTFunDef(a, args, _, _)) if args.nonEmpty =>
        modelFunDefs += a -> me
      case _ =>
    }

    var model = Map[Identifier, Expr]()

    for (me <- smodel) me match {
      case DefineFun(SMTFunDef(s, args, kind, e)) =>
        if(args.isEmpty) {
          variables.getA(s) match {
            case Some(id) =>
              // EK: this is a little hack, we pass models for array functions as let-defs
              try {
                model += id -> fromSMT(e, id.getType)(Map(), modelFunDefs)
              } catch {
                case _ : Unsupported =>

              }
            case _ => // function, should be handled elsewhere
          }
        }
      case _ =>
    }

    new Model(model)
  }

}
