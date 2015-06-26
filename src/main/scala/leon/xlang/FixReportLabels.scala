
package leon
package xlang

import leon.purescala.Definitions.IsLoop
import leon.verification.{VC, VCKinds, VerificationReport}
import leon.xlang.XLangAnalysisPhase.VCXLangKinds._

object FixReportLabels extends LeonPhase[VerificationReport, VerificationReport]{

  override val name: String = "fixReportLabels"
  override val description: String = "Fix verification report labels to reflect the original imperative VCs"

  def run(ctx: LeonContext)(vr: VerificationReport): VerificationReport = {
    //this is enough to convert invariant postcondition and inductive conditions. However the initial validity
    //of the invariant (before entering the loop) will still appear as a regular function precondition
    //To fix this, we need some information in the VCs about which function the precondtion refers to
    //although we could arguably say that the term precondition is general enough to refer both to a loop invariant
    //precondition and a function invocation precondition

    val newResults = for ((vc, ovr) <- vr.results) yield {
      val (vcKind, fd) = vc.fd.flags.collectFirst { case IsLoop(orig) => orig } match {
        case None => (vc.kind, vc.fd)
        case Some(owner) => (vc.kind.underlying match {
          case VCKinds.Precondition => InvariantInd
          case VCKinds.Postcondition => InvariantPost
          case _ => vc.kind
        }, owner)
      }

      val nvc = VC(
        vc.condition,
        fd,
        vcKind,
        vc.tactic
      ).setPos(vc.getPos)

      nvc -> ovr

    }

    VerificationReport(newResults)

  }

}
