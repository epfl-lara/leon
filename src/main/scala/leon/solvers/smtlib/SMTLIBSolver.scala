/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package smtlib

import utils._
import purescala._
import Common._
import Trees._
import Extractors._
import TreeOps._
import TypeTrees._
import Definitions._

import _root_.smtlib.{PrettyPrinter => SMTPrinter, Interpreter => SMTInterpreter}
import _root_.smtlib.Commands.{Identifier => _, Assert => SMTAssert, _}
import _root_.smtlib.CommandResponses.{Error => ErrorResponse, _}
import _root_.smtlib.sexpr.SExprs._
import _root_.smtlib.interpreters._

abstract class SMTLIBSolver(val context: LeonContext,
                            val program: Program)
  extends IncrementalSolver with Interruptible with SMTLIBTarget {

  override def interrupt: Unit = {}
  override def recoverInterrupt(): Unit = {}

  override def name: String = "smt-"+targetName

  override def assertCnstr(expr: Expr): Unit = {
    variablesOf(expr).foreach(declareVariable)
    val sexpr = toSMT(expr)(Map())
    sendCommand(SMTAssert(sexpr))
  }

  override def check: Option[Boolean] = sendCommand(CheckSat) match {
    case CheckSatResponse(SatStatus)     => Some(true)
    case CheckSatResponse(UnsatStatus)   => Some(false)
    case CheckSatResponse(UnknownStatus) => None
  }

  override def getModel: Map[Identifier, Expr] = {
    val syms = variables.bSet.toList
    val cmd: Command = GetValue(syms.head, syms.tail)

    val GetValueResponse(valuationPairs) = sendCommand(cmd)

    valuationPairs.collect {
      case (sym: SSymbol, value) if variables.containsB(sym) =>
        //println("Getting model for "+sym)
        //println("Value "+value)
        (variables.toA(sym), fromSMT(value)(Map()))
    }.toMap
  }

  override def free() = {
    interpreter.free()
    out.close
  }

  override def push(): Unit = {
    sendCommand(Push(1))
  }
  override def pop(lvl: Int = 1): Unit = {
    sendCommand(Pop(1))
  }
}
