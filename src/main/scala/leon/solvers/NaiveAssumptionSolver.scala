/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions._
import purescala.Constructors._

trait NaiveAssumptionSolver extends AssumptionSolver {
  self: IncrementalSolver =>

  var lastBs = Set[Expr]()
  def checkAssumptions(bs: Set[Expr]): Option[Boolean] = {
    push()
    lastBs = bs
    assertCnstr(andJoin(bs.toSeq))
    val res = check
    pop()

    res
  }

  def getUnsatCore: Set[Expr] = {
    lastBs
  }
}
