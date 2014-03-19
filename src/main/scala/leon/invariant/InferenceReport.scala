/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package invariant

import purescala.Definitions.FunDef
import leon.verification._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Common._

class InferenceCondition(val invariant: Option[Expr], funDef: FunDef) 
	extends VerificationCondition(BooleanLiteral(true), funDef, null, null, "") {
        
  value = invariant match {
    case None => None
    case _ => Some(true)
  }
  
  override def status : String = invariant match {
    case None => "unknown"
    case _ => invariant.get.toString    
  }

  override def tacticStr = throw new IllegalStateException("should not be called!")

  override def solverStr = throw new IllegalStateException("should not be called!")

}

class InferenceReport(fvcs: Map[FunDef, List[VerificationCondition]]) 
	extends VerificationReport(fvcs) {      

  override def summaryString : String = if(totalConditions >= 0) {
    InferenceReport.infoHeader +
    conditions.map(InferenceReport.infoLine).mkString("\n", "\n", "\n") +
    InferenceReport.infoSep +
    ("║ total: %-4d   inferred: %-4d   unknown %-4d " +
      (" " * 16) +
      " %7.3f ║\n").format(totalConditions, totalValid, totalUnknown, totalTime) +
    InferenceReport.infoFooter
  } else {
    "No verification conditions were analyzed."
  }
}

object InferenceReport {
  def emptyReport : VerificationReport = new VerificationReport(Map())

  private def fit(str : String, maxLength : Int) : String = {
    if(str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private val infoSep    : String = "╟" + ("┄" * 83) + "╢\n"
  private val infoFooter : String = "╚" + ("═" * 83) + "╝"
  private val infoHeader : String = ". ┌─────────┐\n" +
                                    "╔═╡ Summary ╞" + ("═" * 71) + "╗\n" +
                                    "║ └─────────┘" + (" " * 71) + "║"

  private def infoLine(vc : VerificationCondition) : String = {
    val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")

    "║ %-25s %9s %-8s║".format(
      fit(vc.funDef.id.toString, 25),      
      vc.status,            
      timeStr)
  }
}
