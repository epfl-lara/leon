/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._

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
