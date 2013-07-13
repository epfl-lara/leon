/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Definitions._
import leon.verification._

object XlangAnalysisPhase extends LeonPhase[Program, VerificationReport] {

  val name = "xlang analysis"
  val description = "apply analysis on xlang"

  def run(ctx: LeonContext)(pgm: Program): VerificationReport = {

    val pgm1 = ArrayTransformation(ctx, pgm)
    val pgm2 = EpsilonElimination(ctx, pgm1)
    val (pgm3, wasLoop) = ImperativeCodeElimination.run(ctx)(pgm2)
    val pgm4 = purescala.FunctionClosure.run(ctx)(pgm3)

    def functionWasLoop(fd: FunDef): Boolean = fd.orig match {
      case None => false //meaning, this was a top level function
      case Some(nested) => wasLoop.contains(nested) //could have been a LetDef originally
    }

    var subFunctionsOf = Map[FunDef, Set[FunDef]]().withDefaultValue(Set())
    pgm4.definedFunctions.foreach { fd => fd.parent match {
      case Some(p) =>
        subFunctionsOf += p -> (subFunctionsOf(p) + fd)
      case _ =>
    }}


    val newOptions = ctx.options map {
      case LeonValueOption("functions", ListValue(fs)) => {
        var freshToAnalyse: Set[String] = Set()
        fs.foreach((toAnalyse: String) => {
          pgm.definedFunctions.find(_.id.name == toAnalyse) match {
            case Some(fd) => {
              val children = subFunctionsOf(fd)
              freshToAnalyse ++= children.map(_.id.name)
              freshToAnalyse += fd.id.name
            }
            case None =>
          }
        })

        LeonValueOption("functions", ListValue(freshToAnalyse.toList))
      }
      case opt => opt
    }

    val vr = AnalysisPhase.run(ctx.copy(options = newOptions))(pgm4)
    completeVerificationReport(vr, functionWasLoop _)
  }

  def completeVerificationReport(vr: VerificationReport, functionWasLoop: FunDef => Boolean): VerificationReport = {
    val vcs = vr.conditions

    //this is enough to convert invariant postcondition and inductive conditions. However the initial validity
    //of the invariant (before entering the loop) will still appear as a regular function precondition
    //To fix this, we need some information in the VCs about which function the precondtion refers to
    //although we could arguably say that the term precondition is general enough to refer both to a loop invariant
    //precondition and a function invocation precondition
    var freshFtoVcs = Map[FunDef, List[VerificationCondition]]()

    for (vc <- vcs) {
      val funDef = vc.funDef
      if(functionWasLoop(funDef)) {
        val freshVc = new VerificationCondition(
          vc.condition, 
          funDef.parent.getOrElse(funDef), 
          if(vc.kind == VCKind.Postcondition) VCKind.InvariantPost else if(vc.kind == VCKind.Precondition) VCKind.InvariantInd else vc.kind,
          vc.tactic,
          vc.info).setPosInfo(funDef)
        freshVc.value = vc.value
        freshVc.solvedWith = vc.solvedWith
        freshVc.time = vc.time
        freshFtoVcs += freshVc.funDef -> (freshVc :: freshFtoVcs.getOrElse(freshVc.funDef, List()))
      } else {
        freshFtoVcs += vc.funDef -> (vc :: freshFtoVcs.getOrElse(vc.funDef, List()))
      }
    }

    new VerificationReport(freshFtoVcs)
  }

}
