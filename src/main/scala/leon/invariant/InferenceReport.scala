/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package invariant

import purescala.Definitions.FunDef
import leon.verification._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Definitions._
import leon.purescala.Common._


class InferenceCondition(val invariant: Option[Expr], funDef: FunDef) 
	extends VerificationCondition(BooleanLiteral(true), funDef, null, null, "") {   
  
  override def status : String = invariant match {
    case None => "unknown"
    case Some(inv) => {      
      val prettyInv = Util.replaceInstruVars(inv, funDef)
      prettyInv.toString
    }
  }

  override def tacticStr = throw new IllegalStateException("should not be called!")

  override def solverStr = throw new IllegalStateException("should not be called!")
}

class InferenceReport(fvcs: Map[FunDef, List[VerificationCondition]]) 
	extends VerificationReport(fvcs) {
  
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
  
  override def summaryString : String = if(conditions.size > 0) {    
    val maxTempSize = (conditions.map(_.status.size).max + 3)
    val outputStrs = conditions.map(vc => {
      val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")
      "%-15s %s %-4s".format(fit(vc.funDef.id.toString, 15), vc.status + (" "*(maxTempSize-vc.status.size)), timeStr)
    }) 
    val entrySize = (outputStrs.map(_.size).max + 2)     
    
    infoHeader(entrySize) +
    outputStrs.map(str => infoLine(str, entrySize)).mkString("\n", "\n", "\n") +
    infoSep(entrySize) +
    {
      val summaryStr = "total: %-4d  inferred: %-4d  unknown: %-4d  time: %-3.3f".format(totalConditions, totalValid, totalUnknown, totalTime)
      "║ "+ summaryStr + (" " * (entrySize - summaryStr.size - 2)) + " ║\n"      
    } +    
    infoFooter(entrySize)
  } else {
    "No user provided templates were solved."
  }
}