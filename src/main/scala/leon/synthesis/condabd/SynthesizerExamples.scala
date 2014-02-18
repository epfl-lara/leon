package leon.synthesis.condabd

import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }
import scala.collection.mutable.{ PriorityQueue, ArrayBuffer, HashSet }
import scala.util.control.Breaks._

import leon.{ Reporter, DefaultReporter, LeonContext }
import leon.Main.processOptions

import leon.solvers._
import leon.solvers.z3._

import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Trees.{ Variable => LeonVariable, _ }
import leon.purescala.Definitions.{ TypedFunDef, FunDef, Program, ModuleDef}
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps

import leon.evaluators.EvaluationResults
import leon.evaluators._
import leon.synthesis.{ Problem, SynthesisContext }

import insynth._
import insynth.leon.loader._
import insynth.leon.{ LeonDeclaration => Declaration, _ }
import insynth.reconstruction.Output

import _root_.insynth.{ Solver => _, _ }
import _root_.insynth.engine._
import _root_.insynth.util.logging.HasLogger

import examples._
import evaluation._
import ranking._
import refinement._
import verification._

import SynthesisInfo._
import SynthesisInfo.Action._
import SynthesisContext.SynthesisSolver

// enable postfix operations
import scala.language.postfixOps

class SynthesizerForRuleExamples(
  // some synthesis instance information
  val mainSolver: SolverFactory[SynthesisSolver],
  val program: Program,
  val desiredType: LeonType,
  val tfd: TypedFunDef,
  val problem: Problem,
  val synthesisContext: SynthesisContext,
  val evaluationStrategy: EvaluationStrategy, // = DefaultEvaluationStrategy(program, tfd, synthesisContext.context),
  // number of condition expressions to try before giving up on that branch expression
  numberOfBooleanSnippets: Int = 5,
  numberOfCounterExamplesToGenerate: Int = 5,
//  leonTimeout: Int = 1, // seconds
  analyzeSynthesizedFunctionOnly: Boolean = false,
  showLeonOutput: Boolean = false,
  reporter: Reporter,
  //examples: List[Map[Identifier, Expr]] = Nil,
  // we need the holeDef to know the right ids
  introduceExamples: (() => List[Map[Identifier, Expr]]) = { () => Nil },
  collectCounterExamplesFromLeon: Boolean = false,
  filterOutAlreadySeenBranchExpressions: Boolean = true,
  useStringSetForFilterOutAlreadySeenBranchExpressions: Boolean = true,
  numberOfTestsInIteration: Int = 25,
  numberOfCheckInIteration: Int = 5,
  exampleRunnerSteps: Int = 4000) extends HasLogger {

  def info(message: String) = {
    reporter.info(message)
    super.info(message)
  }
  
  info("Synthesizer:")
  info("numberOfBooleanSnippets: %d".format(numberOfBooleanSnippets))
  info("numberOfCounterExamplesToGenerate: %d".format(numberOfCounterExamplesToGenerate))
//  info("leonTimeout: %d".format(leonTimeout))

  info("holeFunDef: %s".format(tfd))
  info("problem: %s".format(problem.toString))
  
  // flag denoting if a correct body has been synthesized
  private var found = false
  
  // objects used in the synthesis
  private var loader: LeonLoader = _
  private var inSynth: InSynth = _
  private var inSynthBoolean: InSynth = _
  // initial declarations
  private var allDeclarations: List[Declaration] = _

  // can be used to unnecessary syntheses
  private var variableRefinedBranch = false
  private var variableRefinedCondition = true // assure initial synthesis
  private var booleanExpressionsSaved: Stream[Output] = _

  // heuristics that guide the search
  private var variableRefiner: VariableRefiner = _
  private var refiner: Filter = _
  type FilterSet = HashSet[Expr]
  private var seenBranchExpressions: FilterSet = new FilterSet()
  private var successfulCandidates = IndexedSeq[Output]()

  // filtering/ranking with examples support
  var exampleRunner: ExampleRunner = _
  var gatheredExamples: ArrayBuffer[Example] = _
  
  // store initial precondition since it will be overwritten
  private var initialPrecondition: Expr = _
  // accumulate precondition for the remaining branch to synthesize 
  private var accumulatingCondition: Expr = _
  // accumulate the final expression of the hole
  private var accumulatingExpression: Expr => Expr = _

  // information about the synthesis
  private val synthInfo = new SynthesisInfo
  
  val verifier = new RelaxedVerifier(mainSolver, problem, synthInfo)
  import verifier._

  def synthesize: Report = {
    info("Synthesis called on files: " + synthesisContext.context.files)

    // profile
    synthInfo start Synthesis

    info("Initializing synthesizer: ")
    info("numberOfBooleanSnippets: %d".format(numberOfBooleanSnippets))
    info("numberOfCounterExamplesToGenerate: %d".format(numberOfCounterExamplesToGenerate))
//    info("leonTimeout: %d".format(leonTimeout))
    initialize
    info("Synthesizer initialized")

    // keeps status of validity
    var keepGoing = true
    // update flag in case of time limit overdue
    def checkTimeout =
      if (synthesisContext.context.interruptManager.isInterrupted()) {
        info("Timeout occured, stopping this synthesis rules")
        keepGoing = false
        true
      } else
        false

    // initial snippets (will update in the loop)
    var snippets = synthesizeBranchExpressions
    var snippetsIterator = snippets.iterator

    // ordering of expressions according to passed examples
    var pq = getNewExampleQueue

    // iterate while the program is not valid
    import scala.util.control.Breaks._
    var totalExpressionsTested = 0
    var iteration = 0
    var noBranchFoundIteration = 0
    breakable {
      while (keepGoing) {
        if (checkTimeout) break
        // next iteration
        iteration += 1
        noBranchFoundIteration += 1
        info("####################################")
        info("######Iteration #" + iteration + " ###############")
        info("####################################")
        info("# precondition is: " + tfd.precondition.getOrElse(BooleanLiteral(true)))
        info("# accumulatingCondition is: " + accumulatingCondition)
        info("# accumulatingExpression(Unit) is: " + accumulatingExpression(UnitLiteral))
        info("####################################")
        interactivePause

        var numberOfTested = 0

        info("Going into a enumeration/testing phase.")
        fine("evaluating examples: " + gatheredExamples.mkString("\n"))

        breakable {
          while (true) {
            if (checkTimeout) break
            val batchSize = numberOfTestsInIteration * (1 << noBranchFoundIteration)

            info("numberOfTested: " + numberOfTested)
            // ranking of candidates        
            val candidates = {
              val (it1, it2) = snippetsIterator.duplicate
              snippetsIterator = it2.drop(batchSize)
              it1.take(batchSize).
                filterNot(
                  out => {
                    val snip = out.getSnippet
                    fine("enumerated: " + snip)
      							(seenBranchExpressions contains snip) ||
      								refiner.isAvoidable(snip, problem.as)
                  }).toIndexedSeq ++
		            	// adding previous candidates because they may not be enumerated
		              successfulCandidates
            }
            
//            info("Got candidates of size: " + candidates.size +
//              " , first 10 of them are: " + candidates.take(10).map(_.getSnippet.toString).mkString(",\t"))
            info("Got candidates of size: " + candidates.size)            
            fine("Got candidates: " + candidates.map(_.getSnippet.toString).mkString(",\n"))
            interactivePause

            if (candidates.size > 0) {
              // save current precondition and the old body since it will can be mutated during evaluation
              val oldPreconditionSaved = tfd.precondition
              val oldBodySaved = tfd.body
              // set initial precondition
              tfd.fd.precondition = Some(initialPrecondition)

              val ranker = evaluationStrategy.getRanker(candidates, accumulatingExpression, gatheredExamples)
              exampleRunner = evaluationStrategy.getExampleRunner
              
              info("Ranking candidates...")
              synthInfo.start(Action.Evaluation)
              val (maxCandidate, maxCandidateInd) = ranker.getMax
              val (passed, failedModulo) = ranker.fullyEvaluate(maxCandidateInd)
              synthInfo.end

              // get all examples that failed evaluation to filter potential conditions
              val evaluation = evaluationStrategy.getEvaluation
              // evaluate all remaining examples
              for (_ <- exampleRunner.examples.size until
                  				evaluation.getNumberOfEvaluations(maxCandidateInd) by -1)
              	evaluation.evaluate(maxCandidateInd)
              val (evalArray, size) = evaluation.getEvaluationVector(maxCandidateInd)
              assert(size == gatheredExamples.size)
              val (passedExamplesPairs, failedExamplesPairs) = (gatheredExamples zip evalArray).partition {
                case (ex, result) =>
                  result
              }
              val examplesPartition =
                (passedExamplesPairs.map(_._1), failedExamplesPairs.map(_._1))
              
              fine("Failed examples for the maximum candidate: " + examplesPartition)

              // restore original precondition and body
              tfd.fd.precondition = oldPreconditionSaved
              tfd.fd.body = oldBodySaved
              
              // check for timeouts
              if (!keepGoing) break

              info("candidate with the most successfull evaluations is: " + maxCandidate.getExpr +
                " with pass count " + passed + " out of " + gatheredExamples.size)
              interactivePause
              numberOfTested += batchSize
//              interactivePause
              
              val currentCandidateExpr = maxCandidate.getExpr
              if (tryToSynthesizeBranch(currentCandidateExpr, examplesPartition)) {
                //noBranchFoundIteration = 0
                
                // after a branch is synthesized it makes sense to consider candidates that previously failed
                seenBranchExpressions = new FilterSet()
                successfulCandidates +:= candidates(maxCandidateInd)
                
//              			        interactivePause
                break
              } else {
				        // add to seen if branch was not found for it
				        seenBranchExpressions += currentCandidateExpr
              }
    			    interactivePause

              totalExpressionsTested += numberOfTested
              noBranchFoundIteration += 1
            }
          } // while(true)          
        } //  breakable

        if (!keepGoing) break

        // if did not found for any of the branch expressions
        if (found) {
          synthInfo end Synthesis
          synthInfo.iterations = iteration
          synthInfo.numberOfEnumeratedExpressions = numberOfTested
          info("We are done, in time: " + synthInfo.last)
          return new FullReport(tfd, synthInfo)
        }

        if (variableRefinedBranch) {
          info("Variable refined, doing branch synthesis again")
          // get new snippets
          snippets = synthesizeBranchExpressions
          snippetsIterator = snippets.iterator
          pq = getNewExampleQueue

          // reset flag
          variableRefinedBranch = false
        } else
          // reseting iterator needed because we may have some expressions that previously did not work
          snippetsIterator = snippets.iterator

        info("Filtering based on precondition: " + And(initialPrecondition, accumulatingCondition))
        fine("counterexamples before filter: " + gatheredExamples.size)
        exampleRunner.filter(And(initialPrecondition, accumulatingCondition))
        gatheredExamples = exampleRunner.examples
        fine("counterexamples after filter: " + gatheredExamples.size)
        fine("counterexamples after filter: " + gatheredExamples.mkString("\n"))
      }
    } //breakable { while (!keepGoing) {

    EmptyReport
  }

  def generateCounterexamples(program: Program, funDef: FunDef, number: Int): (Seq[Map[Identifier, Expr]], Expr) = {
    info("Generate counter examples with precondition " + funDef.precondition.getOrElse(BooleanLiteral(true)))

    // save current precondition
    var precondition = funDef.precondition.getOrElse(BooleanLiteral(true))
    val preconditionToRestore = funDef.precondition
    // accumulate counterexamples as sequence of maps
    var maps: Seq[Map[Identifier, Expr]] = Seq.empty

    // iterate specific number of times or until no further counterexample can be generated
    var changed = true
    var ind = 0
    while (ind < number && changed) {
      // analyze the program
      val (solved, map) = analyzeFunction(tfd)

      // check if solver could solved this instance
      if (solved == false && !map.isEmpty) {
        info("Found counterexample: " + map)
        // add current counterexample
        maps :+= map

        // prevent this counterexample to re-occur
        val precAddition = Not(
          And(map map { case (id, value) => Equals(LeonVariable(id), value) } toSeq)
        )
        precondition = And(Seq(precondition, precAddition))
        // update precondition        
        funDef.precondition = Some(precondition)
      } else
        changed = false
        
      // add new constraint
      ind += 1
    }

    funDef.precondition = preconditionToRestore
    // return found counterexamples and the formed precondition
    (maps, precondition)
  }

  def getCurrentBuilder = new InitialEnvironmentBuilder(allDeclarations)

  def synthesizeBranchExpressions = {
    info("Invoking synthesis for branch expressions")
    synthInfo.profile(Generation) { inSynth.getExpressions(getCurrentBuilder).distinct }
  }

  def synthesizeBooleanExpressions = {
    info("Invoking synthesis for condition expressions")
    synthInfo.start(Generation)
    if (variableRefinedCondition) {
      // store for later fetch (will memoize values)
      fine("Going into boolean synthesis")
      val stream = inSynthBoolean.getExpressions(getCurrentBuilder)
      fine("Out of boolean synthesis")
      println("stream is here!")
      booleanExpressionsSaved =
        stream.distinct.take(numberOfBooleanSnippets).
          filterNot(expr => refiner.isAvoidable(expr.getSnippet, problem.as))
      // reset flag
      variableRefinedCondition = false
    }

    synthInfo end booleanExpressionsSaved
  }

  def interactivePause = {
//    System.out.println("Press Any Key To Continue...");
//    new java.util.Scanner(System.in).nextLine();
  }

  def getNewExampleQueue = PriorityQueue[(Expr, Int)]()(
    new Ordering[(Expr, Int)] {
      def compare(pair1: (Expr, Int), pair2: (Expr, Int)) =
        pair1._2.compare(pair2._2)
    })

  def initialize = {
    // create new insynth object
    loader = new LeonLoader(program, problem.as, false)
    inSynth = new InSynth(loader, desiredType, true)
    // save all declarations seen
    allDeclarations = inSynth.declarations
    // make conditions synthesizer
    inSynthBoolean = new InSynth(allDeclarations, BooleanType, true)

    // funDef of the hole
    fine("postcondition is: " + tfd.postcondition.get)
    fine("declarations we see: " + allDeclarations.map(_.toString).mkString("\n"))
    //    interactivePause

    // accumulate precondition for the remaining branch to synthesize 
    accumulatingCondition = BooleanLiteral(true)
    // save initial precondition
    initialPrecondition = tfd.precondition.getOrElse(BooleanLiteral(true))
    val holeFunDefBody = tfd.body.get
    // accumulate the final expression of the hole
    accumulatingExpression = (finalExp: Expr) => {      
	    def replaceChoose(expr: Expr) = expr match {
	      case _: Choose => Some(finalExp)
	      case _ => None
	    }
	    
	    //import TreeOps._
      //matchToIfThenElse(searchAndReplace(replaceChoose)(holeFunDefBody))
	    TreeOps.postMap(replaceChoose)(TreeOps.matchToIfThenElse(holeFunDefBody))
    }
    //accumulatingExpressionMatch = accumulatingExpression

    // each variable of super type can actually have a subtype
    // get sine declaration maps to be able to refine them  
    variableRefiner = new VariableRefinerCompose add
      // refiner on structure
  		new VariableRefinerStructure(loader.directSubclassesMap,
				loader.variableDeclarations, loader.classMap, reporter) add
			// refiner that uses execution
			new VariableRefinerExecution(loader.variableDeclarations, loader.classMap)
//  		new VariableSolverRefiner(loader.directSubclassesMap,
//				loader.variableDeclarations, loader.classMap, mainSolver, reporter)

    // calculate cases that should not happen
    refiner = new Filter(program, tfd, variableRefiner)

    gatheredExamples = ArrayBuffer(introduceExamples().map(Example(_)): _*)
    fine("Introduced examples: " + gatheredExamples.mkString("\t"))
  }

  def tryToSynthesizeBranch(snippetTree: Expr, examplesPartition: (Seq[Example], Seq[Example])): Boolean = {
    val (succeededExamples, failedExamples) = examplesPartition
    // replace hole in the body with the whole if-then-else structure, with current snippet tree
    val oldBody = tfd.body.get
    val newBody = accumulatingExpression(snippetTree)
    tfd.fd.body = Some(newBody)

    // precondition
    val oldPrecondition = tfd.precondition.getOrElse(BooleanLiteral(true))
    tfd.fd.precondition = Some(initialPrecondition)

    snippetTree.setType(desiredType)
    //holeFunDef.getBody.setType(hole.desiredType)
    info("Current candidate solution is:\n" + tfd)

    if (failedExamples.isEmpty) {
    	// check if solver could solved this instance
    	fine("Analyzing program for funDef:" + tfd)
    	val (result, map) = analyzeFunction(tfd)
			info("Solver returned: " + result + " with CE " + map)
    	
	    if (result) {
	      // mark the branch found
	      found = true
	
	      info("Wooooooow we have a winner!")
	      info("************************************")
	      info("*********And the winner is**********")
	      info(accumulatingExpression(snippetTree).toString)
	      info("************************************")
	
	      return true
	    } else {
	      gatheredExamples += Example(map)
	    }
    }

    // store appropriate values here, will be update in a finally branch
    var bodyToRestore = oldBody
    var preconditionToRestore = Some(oldPrecondition)

    // because first initial test
    tfd.fd.precondition = preconditionToRestore

    // get counterexamples
//    info("Going to generating counterexamples: " + holeFunDef)
//    val (maps, precondition) = generateCounterexamples(program, holeFunDef, numberOfCounterExamplesToGenerate)
//
//    // collect (add) counterexamples from leon
//    if (collectCounterExamplesFromLeon)
//      gatheredExamples ++= maps.map(Example(_))
    val maps = Seq[Map[Identifier, Expr]]()

    // will modify funDef body and precondition, restore it later
    try {
      { 
        // reconstruct (only defined number of boolean expressions)
        val innerSnippets = synthesizeBooleanExpressions
        // just printing of expressions
        fine(
          (innerSnippets.zipWithIndex map {
            case ((snippet: Output, ind: Int)) => ind + ": snippet is " + snippet.getSnippet
          }).mkString("\n"))
        interactivePause

        // enumerate synthesized boolean expressions and filter out avoidable ones
        for (
          innerSnippetTree <- innerSnippets map { _.getSnippet };
          if (
            {              
              val flag = !refiner.isAvoidable(innerSnippetTree, problem.as)
              if (!flag) fine("Refiner filtered this snippet: " + innerSnippetTree)
              flag
            })
        ) {
          fine("boolean snippet is: " + innerSnippetTree)
          info("Trying: " + innerSnippetTree + " as a condition.")
          val innerPrecFound = tryToSynthesizeBooleanCondition(
            snippetTree, innerSnippetTree,
            // counter examples represent those for which candidate fails
            (failedExamples.map(_.map) ++ maps), succeededExamples.map(_.map)
          )

          info("tryToSynthesizeBooleanCondition returned " + innerPrecFound + " for " + snippetTree)
          if ( innerPrecFound ) {
            // update accumulating expression
            val oldAccumulatingExpression = accumulatingExpression
            val newAccumulatingExpression =
              (finalExpr: Expr) =>
                oldAccumulatingExpression({
                  val innerIf = IfExpr(innerSnippetTree, snippetTree, finalExpr)
                  innerIf.setType(snippetTree.getType)
                  innerIf
                })
  
            accumulatingExpression = newAccumulatingExpression
  
            // update accumulating precondition
            fine("updating accumulatingPrecondition")
            accumulatingCondition = And(Seq(accumulatingCondition, Not(innerSnippetTree)))
            fine("updating hole fun precondition and body (to be hole)")
            // new precondition (restore in finally)
            preconditionToRestore = Some(accumulatingCondition)
  
            val currentBranchCondition = And(Seq(accumulatingCondition, innerSnippetTree))
            val variableRefinementResult = variableRefiner.refine(innerSnippetTree,
              currentBranchCondition, allDeclarations, exampleRunner.getEvaluator)
  
            if (variableRefinementResult._1) {
              info("Variable is refined.")
              allDeclarations = variableRefinementResult._2
  
              // the reason for two flags is for easier management of re-syntheses only if needed 
              variableRefinedBranch = true
              variableRefinedCondition = true
            }
            
            return true
          }

        } // iterating over all boolean solutions

        info("No precondition found for branch expression: " + snippetTree)
        return false

      } // if ( !maps.isEmpty ) {
      // no counter examples, we just say that we cannot do anything
      false
    } // try
    finally {
      // set these to the FunDef
      tfd.fd.precondition = preconditionToRestore
      // restore old body (we accumulate expression)                                
      tfd.fd.body = Some(oldBody)
    }
  }

  /**
   * tries to abduce a new branch
   * @param snippetTree expression candidate
   * @param innerSnippetTree condition candidate
   * @param counterExamples failed examples 
   * @param succExamples successful examples
   * @return whether branch condition is found
   */
  def tryToSynthesizeBooleanCondition(snippetTree: Expr, innerSnippetTree: Expr,
    counterExamples: Seq[Map[Identifier, Expr]], succExamples: Seq[Map[Identifier, Expr]]):
      Boolean = {
    // new condition together with existing precondition
    val newPrecondition = And(Seq(initialPrecondition, accumulatingCondition, innerSnippetTree))
    val newPathCondition = And(Seq(problem.pc, accumulatingCondition, innerSnippetTree))

    // new expression should not be false
//    val notFalseEquivalence = Not(newCondition)
    val isSatisfiable = 
      checkSatisfiabilityNoMod(newPathCondition)
    fine("Is " + newPathCondition + " satisfiable: " + isSatisfiable)

    // continue if our expression is not contradictory
    if (isSatisfiable) {
      // check if synthesized boolean expression implies precondition (counterexamples)        
      var hadRuntimeError = false
      val implyCounterExamplesPre = (false /: counterExamples) {
        case (false, exMapping) =>
          exampleRunner.evaluateToResult(newPrecondition, exMapping) match {
            case EvaluationResults.Successful(BooleanLiteral(false)) => false
            case r =>
//          throw new RuntimeException("should not go here")
              
             // TODO take care of this mess 
				    val newFunId = FreshIdentifier("tempIntroducedFunction22")
				    val newFun = new FunDef(newFunId, tfd.fd.tparams, tfd.fd.returnType, tfd.fd.params)
//				    newFun.precondition = Some(newCondition)
				    newFun.precondition = Some(initialPrecondition)
				    newFun.postcondition = tfd.fd.postcondition
				    
				    def replaceFunDef(expr: Expr) = expr match {
				      case FunctionInvocation(`tfd`, args) =>
				        Some(FunctionInvocation(newFun.typed(tfd.tps), args))
				      case _ => None
				    }
				    
				    val error = Error("Condition flow hit unknown path.")
				    error.setType(snippetTree.getType)
				    val ifInInnermostElse =
				      IfExpr(innerSnippetTree, snippetTree, error)
				    
				    import TreeOps._
//				    println("ifInInnermostElse " + ifInInnermostElse)
//				    println("acc expr before replace: " + accumulatingExpression(ifInInnermostElse))
				    val newBody = postMap(replaceFunDef)(accumulatingExpression(ifInInnermostElse))
				    
				    newFun.body = Some(newBody)
				    
				    assert(newBody.getType != Untyped)
            val resFresh2 = FreshIdentifier("result22", true).setType(newBody.getType)
				
              val (id, post) = newFun.postcondition.get

              val newCandidate = 
				    Let(resFresh2, newBody,
//				      matchToIfThenElse(replace(Map(LeonVariable(id) -> LeonVariable(resFresh2)),
//				        post)))
				        replace(Map(LeonVariable(id) -> LeonVariable(resFresh2)),
                       matchToIfThenElse(post)))
				    finest("New fun for Error evaluation: " + newFun)
//				    println("new candidate: " + newBody)
	
			        val newProgram = program.copy(modules = ModuleDef(FreshIdentifier("result"), List(newFun)) :: program.modules)
//				    println("new program: " + newProgram)
			          
		          val _evaluator = new CodeGenEvaluator(synthesisContext.context, newProgram		              
		              , _root_.leon.codegen.CodeGenParams(maxFunctionInvocations = 500, checkContracts = true))
	
				    	val res = _evaluator.eval(newCandidate, exMapping)
//				    	if (newCandidate.toString contains "tree.value < value")
//				    		interactivePause
				    		
//				    interactivePause
			    		res match {
				    	  case EvaluationResults.RuntimeError("Condition flow hit unknown path.") =>
				    	    hadRuntimeError = true
				    	    false
				    	  case EvaluationResults.Successful(BooleanLiteral(innerRes)) => !innerRes
				    	  case _ =>
				    	    // TODO think about this
				    	    // I put condition into precondition so some examples will be violated?
				    	    println("new evalution got: " + res + " for " + newCandidate + " and " + exMapping + " newFun is " + newFun)
				    	    true
				    	}
				    		
//              fine("Evaluation result for " + newCondition + " on " + exMapping + " is " + r)
//              true
          }
        case _ => true
      }
      
      fine("implyCounterExamplesPre: " + implyCounterExamplesPre)
      
      val implyCounterExamples = if (!implyCounterExamplesPre && hadRuntimeError) {
        ! succExamples.exists( exMapping => {
//          throw new RuntimeException("should not go here")
             // TODO take care of this mess 
				    val newFunId = FreshIdentifier("tempIntroducedFunction22")
				    val newFun = new FunDef(newFunId, tfd.fd.tparams, tfd.fd.returnType, tfd.fd.params)
//				    newFun.precondition = Some(newCondition)
				    newFun.precondition = Some(initialPrecondition)
				    newFun.postcondition = tfd.fd.postcondition
				    
				    def replaceFunDef(expr: Expr) = expr match {
				      case FunctionInvocation(`tfd`, args) =>
				        Some(FunctionInvocation(newFun.typed(tfd.tps), args))
				      case _ => None
				    }
				    
				    val error = Error("Condition flow hit unknown path.")
				    error.setType(snippetTree.getType)
				    val ifInInnermostElse =
				      IfExpr(innerSnippetTree, snippetTree, error)
				    
				    import TreeOps._
				    val newBody = postMap(replaceFunDef)(accumulatingExpression(ifInInnermostElse))
				    
				    newFun.body = Some(newBody)
				    
				    assert(newBody.getType != Untyped)
            val resFresh2 = FreshIdentifier("result22", true).setType(newBody.getType)
				
              val (id, post) = newFun.postcondition.get

              val newCandidate = 
				    Let(resFresh2, newBody,
//				      matchToIfThenElse(replace(Map(LeonVariable(id) -> LeonVariable(resFresh2)),
//				        post)))				        
				        replace(Map(LeonVariable(id) -> LeonVariable(resFresh2)),
                       matchToIfThenElse(post)))
				    finest("New fun for Error evaluation: " + newFun)
//				    println("new candidate: " + newBody)
	
			        val newProgram = program.copy(modules = ModuleDef(FreshIdentifier("result"), List(newFun)) :: program.modules)
//				    println("new program: " + newProgram)
			          
		          val _evaluator = new CodeGenEvaluator(synthesisContext.context, newProgram,		              
		              _root_.leon.codegen.CodeGenParams(maxFunctionInvocations = 500, checkContracts = true))
	
				    	val res = _evaluator.eval(newCandidate, exMapping)
				    	println("for mapping: " + exMapping + "res is: " + res)
//				    	if (newCandidate.toString contains "tree.value < value")
//				    		interactivePause
				    		
				    interactivePause
			    		res match {
				    	  case EvaluationResults.RuntimeError("Condition flow hit unknown path.") =>				    	    
				    	    false
				    	  case EvaluationResults.Successful(BooleanLiteral(innerRes)) => innerRes
				    	  case _ =>
				    	    println("new evalution got: " + res + " for " + newCandidate + " and " + exMapping)
				    	    false
				    	}
      	})
      } else
        implyCounterExamplesPre
      
      
      fine("implyCounterExamples: " + implyCounterExamples)
//      interactivePause
      
      if (!implyCounterExamples) {
        // if expression implies counterexamples add it to the precondition and try to validate program
        tfd.fd.precondition = Some(newPathCondition)
        
        // do analysis
        val (valid, map) = analyzeFunction(tfd)
        // program is valid, we have a branch
        if (valid) {
          // we found a branch
          info("We found a branch, for expression %s, with condition %s.".format(snippetTree, innerSnippetTree))
          
          // found a boolean snippet, break
          true
        } else {
			    // collect (add) counterexamples from leon
			    if (collectCounterExamplesFromLeon && !map.isEmpty)
			      gatheredExamples ++= (map :: Nil).map(Example(_))            
          
          // reset funDef and continue with next boolean snippet
			    false
        }
      } else {
        fine("Solver filtered out the precondition (does not imply counterexamples)")
        false
      }
    } else {// if (!isItAContradiction)
      fine("Solver filtered out the precondition (is not sound)")
      false      
    }
  }

}
	
