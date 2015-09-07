/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Constructors._
import purescala.Definitions._

import _root_.smtlib.common._
import _root_.smtlib.parser.Commands.{Assert => SMTAssert, _}
import _root_.smtlib.parser.Terms.{Identifier => SMTIdentifier, _}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}
import _root_.smtlib.theories._
import _root_.smtlib.interpreters.ProcessInterpreter

abstract class SMTLIBSolver(val context: LeonContext, val program: Program) 
                           extends Solver with SMTLIBTarget with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  /* Reporter */
  protected val reporter = context.reporter

  /* Public solver interface */
  override def assertCnstr(expr: Expr): Unit = if(!hasError) {
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
    val syms = variables.aSet.filter(filter).toList.map(variables.aToB)
    if (syms.isEmpty) {
      Model.empty
    } else {
      try {
        val cmd: Command = GetValue(
          syms.head,
          syms.tail.map(s => QualifiedIdentifier(SMTIdentifier(s)))
        )

        emit(cmd) match {
          case GetValueResponseSuccess(valuationPairs) =>

            new Model(valuationPairs.collect {
              case (SimpleSymbol(sym), value) if variables.containsB(sym) =>
                val id = variables.toA(sym)

                (id, fromSMT(value, id.getType)(Map(), Map()))
            }.toMap)
          case _ =>
            Model.empty //FIXME improve this
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
    functions.pop()
    errors.pop()

    emit(Pop(1))
  }

}
