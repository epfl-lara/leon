/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Expressions._
import verification.VC

import utils.Interruptible
import scala.concurrent._
import scala.concurrent.duration._

import ExecutionContext.Implicits.global

class PortfolioSolver[S <: Solver with Interruptible](val context: LeonContext, val solvers: Seq[S])
        extends Solver with NaiveAssumptionSolver {

  val name = "Pfolio"

  protected var model = Model.empty
  protected var resultSolver: Option[Solver] = None

  override def getResultSolver = resultSolver

  def assertCnstr(expression: Expr): Unit = {
    solvers.foreach(_.assertCnstr(expression))
  }

  override def assertVC(vc: VC): Unit = {
    solvers.foreach(_.assertVC(vc))
  }

  def check: Option[Boolean] = {
    model = Model.empty

    context.reporter.debug("Running portfolio check")
    // solving
    val fs = solvers.map { s =>
      Future {
        val result = s.check
        val model: Model = if (result == Some(true)) {
          s.getModel
        } else {
          Model.empty
        }
        (s, result, model)
      }
    }

    fs.foreach(_ onFailure { case ex: Throwable => ex.printStackTrace() })

    val result = Future.find(fs)(_._2.isDefined)

    val res = Await.result(result, Duration.Inf) match {
      case Some((s, r, m)) =>
        model = m
        resultSolver = s.getResultSolver
        resultSolver.foreach { solv =>
          context.reporter.debug("Solved with "+solv)
        }
        solvers.foreach(_.interrupt())
        r
      case None =>
        context.reporter.debug("No solver succeeded")
        fs.foreach(f => println(f.value))
        None
    }

    fs foreach { Await.ready(_, Duration.Inf) }
    res
  }

  def push(): Unit = {
    solvers.foreach(_.push())
  }

  def pop(): Unit = {
    solvers.foreach(_.pop())
  }

  def free() = {
    solvers.foreach(_.free)
    model = Model.empty
  }

  def getModel: Model = {
    model
  }

  def interrupt(): Unit = {
    solvers.foreach(_.interrupt())
  }

  def recoverInterrupt(): Unit = {
    solvers.foreach(_.recoverInterrupt())
  }

  def reset() = {
    solvers.foreach(_.reset)
    model = Model.empty
  }
}
