/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

trait InterruptibleSolver {
  def halt(): Unit
  def init(): Unit
}
