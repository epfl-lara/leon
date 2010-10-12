package purescala

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._

class InductionTactic(reporter: Reporter) extends DefaultTactic(reporter) {
  override val description = "Induction tactic for suitable functions"
  override val shortDescription = "induction"

  override def generatePostconditions(funDef: FunDef) : Seq[VerificationCondition] = {
    Seq(new VerificationCondition(BooleanLiteral(false), funDef, VCKind.Postcondition, this))
  }
}
