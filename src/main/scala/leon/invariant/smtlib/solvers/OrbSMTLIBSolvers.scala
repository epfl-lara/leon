/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant
package smtlib
package solvers

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.SSymbol
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import utils._
import leon.LeonContext
import leon.solvers.z3
import leon.solvers.cvc4
import leon.solvers.CantResetException
import leon.solvers.Model
import leon.solvers.NaiveAssumptionSolver
import leon.solvers.Solver
import leon.solvers.SolverContext
import leon.solvers.SolverUnsupportedError
import leon.solvers.smtlib.SMTLIBCVC4Component
import leon.solvers.smtlib.SMTLIBTarget
import leon.solvers.smtlib.SMTLIBUnsupportedError
import leon.solvers.smtlib.SMTLIBCVC4Target
import leon.solvers.smtlib.SMTLIBZ3Target

/**
 * Smtlib solvers optimized for use in Orb. In particular, the solvers
 * do not support theories 
 */
abstract class OrbSMTLIBSolver(val sctx: SolverContext, val program: Program) 
                           extends Solver with SMTLIBTarget with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "orb-smt-"+targetName

  override def dbg(msg: => Any) = {
    debugOut foreach { o =>
      o.write(msg.toString)
      o.flush()
    }
  }

  /* Public solver interface */
  def assertCnstr(expr: Expr): Unit = if(!hasError) {
    try {
      variablesOf(expr).foreach(declareVariable)
      val term = toSMT(expr)(Map())
      emit(SMTAssert(term))
    } catch {
      case _ : SMTLIBUnsupportedError =>
        // Store that there was an error. Now all following check()
        // invocations will return None
        addError()
    }
  }

  override def reset() = {
    emit(Reset(), rawOut = true) match {
      case ErrorResponse(msg) =>
        reporter.warning(s"Failed to reset $name: $msg")
        throw new CantResetException(this)
      case _ =>
    }
  }

  override def check: Option[Boolean] = {
    if (hasError) None
    else emit(CheckSat()) match {
      case CheckSatStatus(SatStatus)     => Some(true)
      case CheckSatStatus(UnsatStatus)   => Some(false)
      case CheckSatStatus(UnknownStatus) => None
      case e                             => None
    }
  }

  protected def getModel(filter: Identifier => Boolean): Model = {
    val syms = variables.aSet.filter(filter).map(variables.aToB)
    if (syms.isEmpty) {
      Model.empty
    } else {
      try {
        emit(GetModel()) match {
          case GetModelResponseSuccess(smodel) =>
            // first-pass to gather functions
            val modelFunDefs = smodel.collect {
              case me @ DefineFun(SMTFunDef(a, args, _, _)) if args.nonEmpty =>
                a -> me
            }.toMap
            val model = smodel.flatMap {
              case DefineFun(SMTFunDef(s, _, _, e)) if syms(s) =>
                try {
                  val id = variables.toA(s)
                  val value = fromSMT(e, id.getType)(Map(), modelFunDefs)
                  Some(id-> value)
                } catch {
                  case _: Unsupported => None
                }
              case _ => None
            }.toMap
            new Model(model)
          case _ =>
            Model.empty // FIXME improve this
        }
      } catch {
        case e : SMTLIBUnsupportedError =>
          throw new SolverUnsupportedError(e.t, this, e.reason)
      }
    }
  }

  override def getModel: Model = getModel( _ => true)

  override def push(): Unit = {
    constructors.push()
    selectors.push()
    testers.push()
    variables.push()
    sorts.push()
    lambdas.push()
    functions.push()
    errors.push()

    emit(Push(1))
  }

  override def pop(): Unit = {
    constructors.pop()
    selectors.pop()
    testers.pop()
    variables.pop()    
    sorts.pop()
    lambdas.pop()
    functions.pop()
    errors.pop()

    emit(Pop(1))
  }
}

class OrbSMTLIBZ3Solver(sctx: SolverContext, program: Program)
  extends OrbSMTLIBSolver(sctx, program) with SMTLIBZ3Target with z3.Z3Solver

class OrbSMTLIBCVC4Solver(context: SolverContext, program: Program)
  extends OrbSMTLIBSolver(context, program) with SMTLIBCVC4Target with cvc4.CVC4Solver {

  def targetName = "orb-cvc4"

  def userDefinedOps(ctx: LeonContext) = {
    ctx.findOptionOrDefault(SMTLIBCVC4Component.optCVC4Options)
  }

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--incremental",
//      "--no-incremental",
//      "--tear-down-incremental",
//      "--dt-rewrite-error-sel", // Removing since it causes CVC4 to segfault on some inputs
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt2.5"
    ) ++ userDefinedOps(ctx).toSeq
  }
}
  