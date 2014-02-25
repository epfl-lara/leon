/* Copyright 2009-2013 EPFL, Lausanne */

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

class PortfolioSolver(val context: LeonContext, solvers: Seq[SolverFactory[Solver with Interruptible]])
        extends Solver with Interruptible {

  val name = "Pfolio"

  var constraints = List[Expr]()

  def assertCnstr(expression: Expr): Unit = {
    constraints ::= expression
  }

  private var modelMap = Map[Identifier, Expr]()
  private var solversInsts = Seq[Solver with Interruptible]()

  def check: Option[Boolean] = {
    modelMap = Map()

    // create fresh solvers
    solversInsts = solvers.map(_.getNewSolver)

    // assert
    solversInsts.foreach { s =>
      s.assertCnstr(And(constraints.reverse))
    }

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
        solversInsts.foreach(_.interrupt)
        r
      case None =>
        None
    }

    solversInsts.foreach(_.free)

    res
  }

  def getModel: Map[Identifier, Expr] = {
    modelMap
  }

  def free() = {
    constraints = Nil
  }

  def interrupt(): Unit = {
    solversInsts.foreach(_.interrupt())
  }

  def recoverInterrupt(): Unit = {
    solversInsts.foreach(_.recoverInterrupt())
  }
}
