//package leon.synthesis.condabd
//package rules
//
//import leon.purescala.Trees._
//import leon.purescala.Common._
//import leon.purescala.TypeTrees._
//import leon.purescala.TreeOps._
//import leon.purescala.Extractors._
//import leon.purescala.Definitions._
//import leon.synthesis._
//import leon.solvers.{ Solver, TimeoutSolver }
//import leon.evaluators.CodeGenEvaluator
//
//import examples.InputExamples._
//import evaluation._
//
//import leon.StopwatchCollections
//
//case object ConditionAbductionSynthesisImmediate extends Rule("Condition abduction synthesis (immediate).") {
//  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
//
//    p.xs match {
//      case givenVariable :: Nil =>
//        val solver = new TimeoutSolver(sctx.solver, 500L)
//        val program = sctx.program
//        val reporter = sctx.reporter
//
//        val desiredType = givenVariable.getType
//        val holeFunDef = sctx.functionContext.get
//
//        // temporary hack, should not mutate FunDef
//        val oldPostcondition = holeFunDef.postcondition
//        val oldPrecondition = holeFunDef.precondition
//
//        try {
//          val freshResID = FreshIdentifier("result").setType(holeFunDef.returnType)
//          val freshResVar = Variable(freshResID)
//
//          val codeGenEval = new CodeGenEvaluator(sctx.context, sctx.program)
//          def getInputExamples = {
//            () =>
//              getDataGenInputExamples(codeGenEval, p,
//                200, 6000, Some(p.as)) ++
//                getDataGenInputExamplesRandomIntegers(codeGenEval, p,
//                  200, 6000, Some(p.as) // bound the random geenerator
//                  , 5)
//          }
//
//          val evaluationStrategy = new CodeGenEvaluationStrategy(program, holeFunDef, sctx.context, 1000)
//
//          holeFunDef.postcondition = Some(replace(
//            Map(givenVariable.toVariable -> ResultVariable().setType(holeFunDef.returnType)), p.phi))
//          holeFunDef.precondition = Some(p.pc)
//
//          val synthesizer = new SynthesizerForRuleExamples(
//            solver, solver.getNewSolver, program, desiredType, holeFunDef, p, sctx, evaluationStrategy,
//            20, 1,
//            reporter = reporter,
//            introduceExamples = getInputExamples,
//            numberOfTestsInIteration = 25,
//            numberOfCheckInIteration = 2)
//
//          synthesizer.synthesize match {
//            case EmptyReport => None
//            case FullReport(resFunDef, _) =>
//              List(
//                RuleInstantiation.immediateSuccess(p, this,
//                  Solution(resFunDef.getPrecondition, Set.empty, resFunDef.body.get)))
//          }
//        } finally {
//          holeFunDef.postcondition = oldPostcondition
//          holeFunDef.precondition = oldPrecondition
//        }
//      case _ =>
//        throw new RuntimeException("Rule is not applicable for more than one output variable.")
//        Nil
//    }
//
//  }
//}
