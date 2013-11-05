/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

trait IncrementalSolver extends Solver {
  def push(): Unit
  def pop(lvl: Int = 1): Unit
}

