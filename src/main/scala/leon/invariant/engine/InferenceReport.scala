/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package invariant.engine

import purescala.Definitions.FunDef
import verification._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Common._
import invariant.templateSolvers._
import invariant.factories._
import invariant.util._
import invariant.structure._
import leon.transformations.InstUtil
import leon.purescala.PrettyPrinter


class InferenceCondition(val invariant: Option[Expr], funDef: FunDef)
  extends VC(BooleanLiteral(true), funDef, null) {

  var time : Option[Double] = None

  def status: String = invariant match {
    case None => "unknown"
    case Some(inv) => {
      val prettyInv = simplifyArithmetic(InstUtil.replaceInstruVars(Util.multToTimes(inv),fd))
      PrettyPrinter(prettyInv)
    }
  }
}

class InferenceReport(p: Program, fvcs: Map[FunDef, List[VC]])(implicit ctx: InferenceContext)
  extends VerificationReport(p : Program, Map()) {

  import scala.math.Ordering.Implicits._
  val conditions : Seq[InferenceCondition] =
    fvcs.flatMap(_._2.map(_.asInstanceOf[InferenceCondition])).toSeq.sortBy(vc => vc.fd.id.name)

  private def infoSep(size: Int)    : String = "╟" + ("┄" * size) + "╢\n"
  private def infoFooter(size: Int) : String = "╚" + ("═" * size) + "╝"
  private def infoHeader(size: Int) : String = ". ┌─────────┐\n" +
                                          "╔═╡ Summary ╞" + ("═" * (size - 12)) + "╗\n" +
                                          "║ └─────────┘" + (" " * (size - 12)) + "║"

  private def infoLine(str: String, size: Int) : String = {
    "║ "+ str + (" " * (size - str.size - 2)) + " ║"
  }

  private def fit(str : String, maxLength : Int) : String = {
    if(str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private def funName(fd: FunDef)  = InstUtil.userFunctionName(fd)

  override def summaryString : String = if(conditions.size > 0) {
    val maxTempSize = (conditions.map(_.status.size).max + 3)
    val outputStrs = conditions.map(vc => {
      val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")
      "%-15s %s %-4s".format(fit(funName(vc.fd), 15), vc.status + (" "*(maxTempSize-vc.status.size)), timeStr)
    })
    val summaryStr = {
      val totalTime = conditions.foldLeft(0.0)((a, ic) => a + ic.time.getOrElse(0.0))
      val inferredConds = conditions.count((ic) => ic.invariant.isDefined)
      "total: %-4d  inferred: %-4d  unknown: %-4d  time: %-3.3f".format(
        conditions.size, inferredConds, conditions.size - inferredConds, totalTime)
    }
    val entrySize = (outputStrs :+ summaryStr).map(_.size).max + 2

    infoHeader(entrySize) +
    outputStrs.map(str => infoLine(str, entrySize)).mkString("\n", "\n", "\n") +
    infoSep(entrySize) +
    infoLine(summaryStr, entrySize) + "\n" +
    infoFooter(entrySize)

  } else {
    "No user provided templates were solved."
  }
}