/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.test._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

import leon.solvers._
import leon.solvers.z3._

trait LeonSolverSuite extends LeonTestSuiteWithProgram {
  def getSolver(implicit ctx: LeonContext, pgm: Program): Solver

  case class SolverDSL(res: Option[Boolean], solver: Solver) {
    val resToString = res match {
      case Some(true)  => "sat"
      case Some(false) => "unsat"
      case None        => "unknown"
    }

    def sat: Unit = {
      if (res != Some(true)) {
        fail(s"Expected 'sat', got '$resToString' from $solver")
      }
    }

    def unsat: Unit = {
      if (res != Some(false)) {
        fail(s"Expected 'unsat', got '$resToString' from $solver")
      }
    }
    def unknown: Unit = {
      if (res != None) {
        fail(s"Expected 'unknown', got '$resToString' from $solver")
      }
    }
  }

  def satToString(res: Option[Boolean]) = res match {
    case Some(true)  => "sat"
    case Some(false) => "unsat"
    case None        => "unknown"
  }

  def validToString(res: Option[Boolean]) = res match {
    case Some(true)  => "invalid"
    case Some(false) => "valid"
    case None        => "unknown"
  }

  def check(cnstr: Expr)(implicit ctx: LeonContext, pgm: Program): Option[Boolean] = {
    val solver = getSolver

    try {
      solver.assertCnstr(cnstr)
      solver.check
    } finally {
      solver.free()
    }
  }

  def sat(cnstr: Expr)(implicit ctx: LeonContext, pgm: Program): Unit = {
    val res = check(cnstr)
    if (res != Some(true)) {
      fail("Expected '"+satToString(Some(true))+"', got '"+satToString(res)+"'")
    }
  }

  def unsat(cnstr: Expr)(implicit ctx: LeonContext, pgm: Program): Unit = {
    val res = check(cnstr)
    if (res != Some(false)) {
      fail("Expected '"+satToString(Some(false))+"', got '"+satToString(res)+"'")
    }
  }

  def valid(cnstr: Expr)(implicit ctx: LeonContext, pgm: Program): Unit = {
    val res = check(Not(cnstr))
    if (res != Some(false)) {
      fail("Expected '"+validToString(Some(false))+"', got '"+validToString(res)+"'")
    }
  }

  def invalid(cnstr: Expr)(implicit ctx: LeonContext, pgm: Program): Unit = {
    val res = check(Not(cnstr))
    if (res != Some(true)) {
      fail("Expected '"+validToString(Some(true))+"', got '"+validToString(res)+"'")
    }
  }

}
