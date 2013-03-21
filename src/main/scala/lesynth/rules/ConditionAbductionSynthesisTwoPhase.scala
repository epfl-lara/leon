package lesynth
package rules

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.purescala.Extractors._
import leon.purescala.Definitions._
import leon.synthesis._
import leon.solvers.{ Solver, TimeoutSolver }

import InputExamples._
import lesynth.SynthesizerForRuleExamples

case object ConditionAbductionSynthesisTwoPhase extends Rule("Condition abduction synthesis (two phase).") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    p.xs match {
      case givenVariable :: Nil =>
        List(new RuleInstantiation(p, this, SolutionBuilder.none, "Condition abduction") {
          def apply(sctx: SynthesisContext): RuleApplicationResult = {
            try {
              val solver = new TimeoutSolver(sctx.solver, 2000L)
              val program = sctx.program
              val reporter = sctx.reporter

              val desiredType = givenVariable.getType
              val holeFunDef = sctx.functionContext.get

              // temporary hack, should not mutate FunDef
              val oldPostcondition = holeFunDef.postcondition
              val oldPrecondition = holeFunDef.precondition
              
              try {
                val freshResID = FreshIdentifier("result").setType(holeFunDef.returnType)
                val freshResVar = Variable(freshResID)
                
                holeFunDef.postcondition = Some(replace(
                  Map(givenVariable.toVariable -> ResultVariable().setType(holeFunDef.returnType)), p.phi))
                holeFunDef.precondition = Some(p.pc)

                val synthesizer = new SynthesizerForRuleExamples(
                  solver, program, desiredType, holeFunDef, p, freshResVar,
                  20, 2, 1,
                  reporter = reporter,
                  introduceExamples = getInputExamples)

                synthesizer.synthesize match {
                  case EmptyReport => RuleApplicationImpossible
                  case FullReport(resFunDef, _) =>
                    RuleSuccess(Solution(resFunDef.getPrecondition, Set.empty, resFunDef.body.get))
                }
              } catch {
                case e: Throwable =>
                  sctx.reporter.warning("Condition abduction crashed: " + e.getMessage)
                  e.printStackTrace
                  RuleApplicationImpossible
              } finally {
                holeFunDef.postcondition = oldPostcondition
                holeFunDef.precondition = oldPrecondition
              }
            }
          }
        })
      case _ =>
        throw new RuntimeException("should not")
        Nil
    }
  }
}
