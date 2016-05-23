/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._

import _root_.smtlib.parser.Commands.{Assert => SMTAssert, FunDef => SMTFunDef, _}
import _root_.smtlib.parser.Terms.{Identifier => _, _}
import _root_.smtlib.parser.CommandsResponses.{Error => ErrorResponse, _}

import theories._
import utils._

abstract class SMTLIBSolver(val sctx: SolverContext, val program: Program, theories: TheoryEncoder)
                           extends Solver with SMTLIBTarget with NaiveAssumptionSolver {

  /* Solver name */
  def targetName: String
  override def name: String = "smt-"+targetName

  private val ids = new IncrementalBijection[Identifier, Identifier]()

  override def dbg(msg: => Any) = {
    debugOut foreach { o =>
      o.write(msg.toString)
      o.flush()
    }
  }

  /* Public solver interface */
  def assertCnstr(raw: Expr): Unit = if (!hasError) {
    try {
      val bindings = variablesOf(raw).map(id => id -> ids.cachedB(id)(theories.encode(id))).toMap
      val expr = theories.encode(raw)(bindings)
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
                  Some(ids.getAorElse(id, id) -> theories.decode(value)(variablesOf(value).map(id => id -> ids.toA(id)).toMap))
                } catch {
                  case _: Unsupported =>
                    None
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

  override def getModel: Model = getModel(_ => true)

  override def push(): Unit = {
    ids.push()
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
    ids.pop()
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
