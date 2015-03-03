/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._
import purescala.Constructors._

import xlang.Trees._
import xlang.TreeOps.isXLang

object NoXLangFeaturesChecking extends UnitPhase[Program] {

  val name = "no-xlang"
  val description = "Ensure and enforce that no xlang features are used"

  override def apply(ctx: LeonContext, pgm: Program): Unit = {
    pgm.definedFunctions.foreach(fd => {
      if(isXLang(fd.fullBody)) {
        ctx.reporter.fatalError(fd.fullBody.getPos, "Expr is using xlang features")
      }
    })
  }

}

