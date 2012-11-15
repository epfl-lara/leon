package leon
package solvers

import Extensions.Extension

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

abstract class Solver(val reporter: Reporter) extends Extension(reporter) {
  // This can be used by solvers to "see" the programs from which the
  // formulas come. (e.g. to set up some datastructures for the defined
  // ADTs, etc.) 
  // Ideally, we would pass it at construction time and not change it later.
  def setProgram(program: Program) : Unit = {}

  // Returns Some(true) if valid, Some(false) if invalid,
  // None if unknown.
  // should halt as soon as possible with any result (Unknown is ok) as soon as forceStop is true
  def solve(expression: Expr) : Option[Boolean]

  def solveOrGetCounterexample(expression : Expr) : (Option[Boolean],Map[Identifier,Expr]) = (solve(expression), Map.empty)

  def solveSAT(expression: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    solveOrGetCounterexample(Not(expression)) match {
      case (Some(true), _) =>
        (Some(false), Map())
      case (Some(false), model) =>
        (Some(true), model)
      case (None, _) =>
        (None, Map())
    }
  }

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    solveSAT(And(expression +: assumptions.toSeq)) match {
      case (Some(false), _) =>
        (Some(false), Map(), assumptions)
      case (r, m) =>
        (r, m, Set())
    }
  }

  def superseeds : Seq[String] = Nil

  private var _forceStop = false

  def halt() : Unit = {
    _forceStop = true
  }

  def init() : Unit = {
    _forceStop = false
  }

  protected def forceStop = _forceStop
}

