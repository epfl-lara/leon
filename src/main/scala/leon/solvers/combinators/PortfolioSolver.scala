/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import utils.Interruptible
import scala.concurrent._
import scala.concurrent.duration._

import scala.collection.mutable.{Map=>MutableMap}

import ExecutionContext.Implicits.global

class PortfolioSolver(val context: LeonContext, solvers: Seq[SolverFactory[AssumptionSolver with IncrementalSolver with Interruptible]])
        extends Solver with IncrementalSolver with Interruptible with NaiveAssumptionSolver {

  val name = "Pfolio"

  var constraints = List[Expr]()

  private var modelMap = Map[Identifier, Expr]()
  private var solversInsts = solvers.map(_.getNewSolver)

  def assertCnstr(expression: Expr): Unit = {
    solversInsts.foreach(_.assertCnstr(expression))
  }

  def push(): Unit = {
    solversInsts.foreach(_.push())
  }

  def pop(lvl: Int): Unit = {
    solversInsts.foreach(_.pop(lvl))
  }

  def check: Option[Boolean] = {
    modelMap = Map()

    context.reporter.debug("Running portfolio check")
    // solving
    val fs = solversInsts.map { s =>
      Future {
        (s, s.check, s.getModel)
      }
    }

    val result = Future.find(fs)(_._2.isDefined)

    val res = Await.result(result, 10.days) match {
      case Some((s, r, m)) =>
        modelMap = m
        context.reporter.debug("Solved with "+s.name)
        solversInsts.foreach(_.interrupt)
        r
      case None =>
        None
    }

    // Block until all solvers finished
    Await.result(Future.fold(fs)(0){ (i, r) => i+1 }, 10.days);

    res
  }

  def free() = {
    solversInsts.foreach(_.free)
    solversInsts = Nil
    modelMap = Map()
    constraints = Nil
  }

  def getModel: Map[Identifier, Expr] = {
    modelMap
  }

  def interrupt(): Unit = {
    solversInsts.foreach(_.interrupt())
  }

  def recoverInterrupt(): Unit = {
    solversInsts.foreach(_.recoverInterrupt())
  }
}
