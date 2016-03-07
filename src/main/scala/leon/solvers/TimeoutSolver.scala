/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Expressions.Expr

import scala.concurrent.duration._

trait TimeoutSolver extends Solver {

  val ti = new TimeoutFor(this)

  var optTimeout: Option[Long] = None

  def setTimeout(timeout: Long): this.type = {
    optTimeout = Some(timeout)
    this
  }

  def setTimeout(timeout: Duration): this.type = {
    optTimeout = Some(timeout.toMillis)
    this
  }

  abstract override def check: Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        ti.interruptAfter(to) {
          super.check
        }
      case None =>
        super.check
    }
  }

  abstract override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        ti.interruptAfter(to) {
          super.checkAssumptions(assumptions)
        }
      case None =>
        super.checkAssumptions(assumptions)
    }
  }

}
