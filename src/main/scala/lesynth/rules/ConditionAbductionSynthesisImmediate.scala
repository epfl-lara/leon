package lesynth
package rules

import leon.purescala.Trees._
import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.TreeOps._
import leon.purescala.Extractors._
import leon.purescala.Definitions._
import leon.synthesis.{ Rule, RuleInstantiation, SynthesisContext, Problem, Solution }
import InputExamples._
import lesynth.SynthesizerForRuleExamples

case object ConditionAbductionSynthesisImmediate extends Rule("Condition abduction synthesis (immediate).") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation]= {
    val solver = sctx.solver
		val program = sctx.program
		val reporter = sctx.reporter
						
		p.xs match {
      case givenVariable :: Nil =>
        val desiredType = givenVariable.getType
        val holeFunDef = sctx.functionContext.get
        
        // temporary hack, should not mutate FunDef
        val oldPostcondition = holeFunDef.postcondition
        val oldPrecondition = holeFunDef.precondition
        try {
          val freshResID = FreshIdentifier("result").setType(holeFunDef.returnType)
          val freshResVar = Variable(freshResID)
	        holeFunDef.postcondition = Some(replace(
            Map(givenVariable.toVariable -> ResultVariable().setType(holeFunDef.returnType)), p.phi)
          )
	        holeFunDef.precondition = Some(p.pc)
	        
	        val synthesizer = new SynthesizerForRuleExamples(
	          solver, program, desiredType, holeFunDef, p, sctx, freshResVar,
	          reporter = reporter,
	          introduceExamples = introduceTwoListArgumentsExamples
	        )
	        
	        synthesizer.synthesize match {
	          case EmptyReport => None
	          case FullReport(resFunDef, _) =>        
			        List(
			          RuleInstantiation.immediateSuccess(p, this,
			            Solution(resFunDef.getPrecondition, Set.empty, resFunDef.body.get)
			          )
			        )
	        }
        } finally {          
	        holeFunDef.postcondition = oldPostcondition
	        holeFunDef.precondition = oldPrecondition
        }
      case _ =>
        throw new RuntimeException("should not")
        Nil
    }
    
  }
}
