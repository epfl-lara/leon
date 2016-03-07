/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions._
import purescala.Constructors._

trait NaiveAssumptionSolver {
  self: Solver =>

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
