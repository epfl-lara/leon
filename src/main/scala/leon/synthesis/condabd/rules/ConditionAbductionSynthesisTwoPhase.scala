package leon.synthesis.condabd
package rules

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.purescala.Extractors._
import leon.purescala.Definitions._
import leon.synthesis._
import leon.solvers._
import leon.evaluators.CodeGenEvaluator

import examples.InputExamples._
import evaluation._

import leon.StopwatchCollections

case object ConditionAbductionSynthesisTwoPhase extends Rule("Condition abduction synthesis (two phase).") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {

    p.xs match {
      case givenVariable :: Nil =>
        List(new RuleInstantiation(p, this, SolutionBuilder.none, "Condition abduction") {
          def apply(sctx: SynthesisContext): RuleApplicationResult = {
            try {
              val solver = SolverFactory(() => sctx.newSolver.setTimeout(500L))
              val program = sctx.program
              val reporter = sctx.reporter

              val desiredType = givenVariable.getType
              val fd = sctx.functionContext.get
              val tfd = fd.typed(fd.tparams.map(_.tp))

              // temporary hack, should not mutate FunDef
              val oldPostcondition = fd.postcondition

              try {
                val freshResID = FreshIdentifier("result").setType(tfd.returnType)
                val freshResVar = Variable(freshResID)

                val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
                def getInputExamples = {
                  () =>
                    //getDataGenInputExamples(sctx.context, sctx.program, codeGenEval, p, 
                    //  100, 6000, Some(p.as)) ++
                    getDataGenInputExamplesRandomIntegers(sctx.context, sctx.program, codeGenEval, p, 
                        100, 6000, Some(p.as)
                        // bound the random geenerator
                        ,10)
                }

                val evaluationStrategy = new CodeGenEvaluationStrategy(program, tfd, sctx.context, 5000)
                fd.postcondition = Some((givenVariable, p.phi))

                val synthesizer = new SynthesizerForRuleExamples(
                  solver, program, desiredType, tfd, p, sctx, evaluationStrategy,
                  20, 1, 
                  reporter = reporter,
                  introduceExamples = getInputExamples,  
                                  numberOfTestsInIteration = 25,
                                  numberOfCheckInIteration = 2
                              )

                synthesizer.synthesize match {
                  case EmptyReport => RuleApplicationImpossible
                  case fr@FullReport(resFunDef, _) =>
                    println(fr.summaryString)
                    println("Compilation time: " + StopwatchCollections.get("Compilation").getMillis)
                    RuleSuccess(
                      Solution(BooleanLiteral(true), Set.empty, Tuple(Seq(resFunDef.body.get))),
                            isTrusted = !synthesizer.verifier.isTimeoutUsed
                    )
                }
              } catch {
                case e: Throwable =>
                  sctx.reporter.warning("Condition abduction crashed: " + e.getMessage)
                  e.printStackTrace
                  RuleApplicationImpossible
              } finally {
                fd.postcondition = oldPostcondition
              }
            }
          }
        })
      case _ =>
        Nil
    }
  }
}
