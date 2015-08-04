/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions.Expr

trait ResettableSolver extends Solver {
  def reset()
}
