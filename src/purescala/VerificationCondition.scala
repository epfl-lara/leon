package purescala

import purescala.Extensions._
import purescala.Trees._
import purescala.Definitions._

/** This is just to hold some history information. */
class VerificationCondition(val condition: Expr, val funDef: FunDef, val kind: VCKind.Value, val tactic: Tactic, val info: String = "") {
  // None = still unknown
  // Some(true) = valid
  // Some(false) = valid
  var value : Option[Boolean] = None
  var solvedWith : Option[Solver] = None
  var time : Option[Double] = None

  def status : String = value match {
    case None => "unknown"
    case Some(true) => "valid"
    case Some(false) => "invalid"
  }

  private def tacticStr = tactic.shortDescription match {
    case "default" => ""
    case s => s
  }

  private def solverStr = solvedWith match {
    case Some(s) => s.shortDescription
    case None => ""
  }

  private def timeStr = time.map(t => "%-3.3f".format(t)).getOrElse("")

  def infoLine : String = {
    "║ %-20s %-10s %-8s %-10s %-7s %7s ║" format (funDef.id.toString, kind, status, tacticStr, solverStr, timeStr)
  }
}

object VerificationCondition {
  val infoFooter : String = "╚" + ("═" * 69) + "╝"
  val infoHeader : String = ". ┌─────────┐\n" +
                            "╔═╡ Summary ╞" + ("═" * 57) + "╗\n" +
                            "║ └─────────┘" + (" " * 57) + "║"
}

object VCKind extends Enumeration {
  val Precondition = Value("precond.")
  val Postcondition = Value("postcond.")
  val ExhaustiveMatch = Value("match.")
}
