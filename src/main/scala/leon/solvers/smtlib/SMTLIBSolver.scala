/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._

import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}

abstract class SMTLIBSolver(val context: LeonContext, val program: Program) 
                           extends Solver with SMTLIBTarget with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

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
        val cmd = GetModel()

        emit(cmd) match {
          case GetModelResponseSuccess(smodel) =>
            var modelFunDefs = Map[SSymbol, DefineFun]()

            // first-pass to gather functions
            for (me <- smodel) me match {
              case me @ DefineFun(SMTFunDef(a, args, _, _)) if args.nonEmpty =>
                modelFunDefs += a -> me
              case _ =>
            }

            var model = Map[Identifier, Expr]()

            for (me <- smodel) me match {
              case DefineFun(SMTFunDef(s, args, kind, e)) if syms(s) =>
                val id = variables.toA(s)
                model += id -> fromSMT(e, id.getType)(Map(), modelFunDefs)
              case _ =>
            }

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
    genericValues.push()
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
    genericValues.pop()
    sorts.pop()
    lambdas.pop()
    functions.pop()
    errors.pop()

    emit(Pop(1))
  }

}
