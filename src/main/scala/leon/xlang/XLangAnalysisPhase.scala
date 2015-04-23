/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Definitions._
import leon.verification._

object XLangAnalysisPhase extends LeonPhase[Program, VerificationReport] {

  val name = "xlang analysis"
  val description = "apply analysis on xlang"

  object VCXLangKinds {
    case object InvariantPost extends VCKind("invariant postcondition", "inv. post.")
    case object InvariantInd  extends VCKind("invariant inductive",     "inv. ind.")
  }

  def run(ctx: LeonContext)(pgm: Program): VerificationReport = {

    ArrayTransformation(ctx, pgm) // In-place
    EpsilonElimination(ctx, pgm)  // In-place
    val (pgm1, wasLoop) = ImperativeCodeElimination.run(ctx)(pgm)
    val pgm2 = purescala.FunctionClosure.run(ctx)(pgm1)

    def functionWasLoop(fd: FunDef): Boolean = fd.orig match {
      case Some(nested) => // could have been a LetDef originally
        wasLoop.contains(nested)
      case _ => false //meaning, this was a top level function
    }

    var subFunctionsOf = Map[FunDef, Set[FunDef]]().withDefaultValue(Set())
    pgm2.definedFunctions.foreach { fd => fd.owner match {
      case Some(p : FunDef) =>
        subFunctionsOf += p -> (subFunctionsOf(p) + fd)
      case _ =>
    }}


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
    completeVerificationReport(vr, functionWasLoop)
  }

  def completeVerificationReport(vr: VerificationReport, functionWasLoop: FunDef => Boolean): VerificationReport = {

    //this is enough to convert invariant postcondition and inductive conditions. However the initial validity
    //of the invariant (before entering the loop) will still appear as a regular function precondition
    //To fix this, we need some information in the VCs about which function the precondtion refers to
    //although we could arguably say that the term precondition is general enough to refer both to a loop invariant
    //precondition and a function invocation precondition

    val newResults = for ((vc, ovr) <- vr.results) yield {
      if(functionWasLoop(vc.fd)) {
        val nvc = VC(vc.condition, 
                     vc.fd.owner match {
                       case Some(fd: FunDef) => fd
                       case _ => vc.fd
                     },
                     vc.kind.underlying match {
                       case VCKinds.Postcondition => VCXLangKinds.InvariantPost
                       case VCKinds.Precondition => VCXLangKinds.InvariantInd
                       case _ => vc.kind
                     },
                     vc.tactic)

        nvc -> ovr
      } else {
        vc -> ovr
      }
    }

    VerificationReport(newResults)
  }

}
