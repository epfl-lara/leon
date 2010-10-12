package purescala

import purescala.Trees._
import purescala.Definitions._
import Extensions.Tactic

class DefaultTactic(reporter: Reporter) extends Tactic(reporter) {
    val description = "Default verification condition generation approach"
    override val shortDescription = "default"

    def generatePostconditions(function: FunDef) : Seq[Expr] = {
      Seq.empty
    }

    def generatePreconditions(function: FunDef) : Seq[Expr] = {
      Seq.empty
    }

    def generatePatternMatchingExhaustivenessChecks(function: FunDef) : Seq[Expr] = {
      Seq.empty
    }

    def generateMiscCorrectnessConditions(function: FunDef) : Seq[Expr] = {
      Seq.empty
    }
}
