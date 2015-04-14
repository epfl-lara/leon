/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import utils._

trait TimeoutSolver extends Solver with Interruptible {

  val ti = new TimeoutFor(this)

  protected var optTimeout: Option[Long] = None

  def setTimeout(timeout: Long): this.type = {
    optTimeout = Some(timeout)
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

}
