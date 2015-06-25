/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Definitions._
import leon.verification._

import leon.utils._

object XLangAnalysisPhase extends LeonPhase[Program, VerificationReport] {

  val name = "xlang analysis"
  val description = "apply analysis on xlang"

  object VCXLangKinds {
    // TODO: something of this sort should be included
    // case object InvariantEntry extends VCKind("invariant init",           "inv. init.")
    case object InvariantPost extends VCKind("invariant postcondition", "inv. post.")
    case object InvariantInd  extends VCKind("invariant inductive",     "inv. ind.")
  }

  def run(ctx: LeonContext)(pgm: Program): VerificationReport = {

    ArrayTransformation(ctx, pgm) // In-place
    EpsilonElimination(ctx, pgm)  // In-place
    val pgm1 = ImperativeCodeElimination.run(ctx)(pgm)
    val pgm2 = purescala.FunctionClosure.run(ctx)(pgm1)

    if (ctx.reporter.isDebugEnabled(DebugSectionTrees)) {
      PrintTreePhase("Program after xlang transformations").run(ctx)(pgm2)
    }

    val subFunctionsOf = Map[FunDef, Set[FunDef]]().withDefaultValue(Set())

    val newOptions = ctx.options map {
      case LeonOption(SharedOptions.optFunctions, fs) => {
        var freshToAnalyse: Set[String] = Set()
        fs.asInstanceOf[Seq[String]].foreach((toAnalyse: String) => {
          pgm.definedFunctions.find(_.id.name == toAnalyse) match {
            case Some(fd) => {
              val children = subFunctionsOf(fd)
              freshToAnalyse ++= children.map(_.id.name)
              freshToAnalyse += fd.id.name
            }
            case None =>
          }
        })

        LeonOption(SharedOptions.optFunctions)(freshToAnalyse.toList)
      }
      case opt => opt
    }

    val vr = AnalysisPhase.run(ctx.copy(options = newOptions))(pgm2)
    completeVerificationReport(vr)
  }

  def completeVerificationReport(vr: VerificationReport): VerificationReport = {

    //this is enough to convert invariant postcondition and inductive conditions. However the initial validity
    //of the invariant (before entering the loop) will still appear as a regular function precondition
    //To fix this, we need some information in the VCs about which function the precondtion refers to
    //although we could arguably say that the term precondition is general enough to refer both to a loop invariant
    //precondition and a function invocation precondition

    val newResults = for ((vc, ovr) <- vr.results) yield {
      val (vcKind, fd) = vc.fd.flags.collectFirst { case IsLoop(orig) => orig } match {
        case None => (vc.kind, vc.fd)
        case Some(owner) => (vc.kind.underlying match {
          case VCKinds.Precondition => VCXLangKinds.InvariantInd
          case VCKinds.Postcondition => VCXLangKinds.InvariantPost
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
