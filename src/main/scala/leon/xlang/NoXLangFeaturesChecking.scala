/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._
import purescala.Constructors._

import purescala.TreeOps.exists
import xlang.Trees._

object NoXLangFeaturesChecking extends UnitPhase[Program] {

  val name = "no-xlang"
  val description = "Ensure and enforce that no xlang features are used"

  private def isXlangExpr(expr: Expr): Boolean = expr match {

    case Block(_, _) => true

    case Assignment(_, _) => true

    case While(_, _) => true

    case Epsilon(_, _) => true

    case EpsilonVariable(_, _) => true

    case LetVar(_, _, _) => true

    case Waypoint(_, _, _) => true

    case ArrayUpdate(_, _, _) => true 

    case _ => false

  }

  override def apply(ctx: LeonContext, pgm: Program): Unit = {
    pgm.definedFunctions.foreach(fd => {
      if(exists(isXlangExpr)(fd.fullBody)) {
        ctx.reporter.fatalError(fd.fullBody.getPos, "Expr is using xlang features")
      }
    })
  }

}

