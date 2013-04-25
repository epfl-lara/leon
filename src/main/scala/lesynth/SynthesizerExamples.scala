package lesynth

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.PriorityQueue

import leon.{Reporter, DefaultReporter, SilentReporter, LeonContext}
import leon.solvers.{ Solver, TimeoutSolver }
import leon.solvers.z3.{ FairZ3Solver }
import leon.verification.AnalysisPhase
import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Trees.{ Variable => LeonVariable, _ }
import leon.purescala.Definitions.{FunDef, Program}
import leon.purescala.Common.{ Identifier, FreshIdentifier }
import leon.purescala.TreeOps

import insynth.util.logging.HasLogger
import insynth.interfaces.Declaration
import insynth.InSynth
import insynth.leon.loader.LeonLoader
import insynth.leon.LeonDeclaration
import insynth.leon.ImmediateExpression
import insynth.engine.InitialEnvironmentBuilder
import insynth.interfaces.Declaration
import insynth.engine.InitialEnvironmentBuilder
import insynth.leon.TypeTransformer
import insynth.reconstruction.Output
import leon.synthesis.{ Problem, SynthesisContext }
import leon.Main.processOptions
import leon.purescala.TypeTrees._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}
import scala.util.control.Breaks.break
import scala.util.control.Breaks.breakable

import SynthesisInfo._
import SynthesisInfo.Action._

class SynthesizerForRuleExamples(    
  // some synthesis instance information
  val solver: Solver,
  val program: Program,
  val desiredType: LeonType,
  val holeFunDef: FunDef,
  val problem: Problem,
  val synthesisContext: SynthesisContext,
  val freshResVar: LeonVariable,
  // number of condition expressions to try before giving up on that branch expression
  numberOfBooleanSnippets: Int = 5,
  numberOfCounterExamplesToGenerate: Int = 5,
  leonTimeout: Int = 2, // seconds
  analyzeSynthesizedFunctionOnly: Boolean = false,
  showLeonOutput: Boolean = false,
  reporter: Reporter = new DefaultReporter,
  //examples: List[Map[Identifier, Expr]] = Nil,
  // we need the holeDef to know the right ids
  introduceExamples: ((Seq[Identifier], LeonLoader) => List[Map[Identifier, Expr]]) = { (_, _) => Nil },
  collectCounterExamplesFromLeon: Boolean = false,
  filterOutAlreadySeenBranchExpressions: Boolean = true,
  useStringSetForFilterOutAlreadySeenBranchExpressions: Boolean = true,  
  numberOfTestsInIteration: Int = 50,
  numberOfCheckInIteration: Int = 5
) extends HasLogger {
  
  val fileName: String = "noFileName"

  info("Synthesizer:")
  info("fileName: %s".format(fileName))
  info("numberOfBooleanSnippets: %d".format(numberOfBooleanSnippets))
  info("numberOfCounterExamplesToGenerate: %d".format(numberOfCounterExamplesToGenerate))
  info("leonTimeout: %d".format(leonTimeout))
  //info("examples: " + examples.mkString(", "))
  
  info("holeFunDef: %s".format(holeFunDef))
  info("problem: %s".format(problem.toString))

  private var hole: Hole = _
  // initial declarations
  private var allDeclarations: List[Declaration] = _
  // objects used in the synthesis
  private var loader: LeonLoader = _
  private var inSynth: InSynth = _
  private var inSynthBoolean: InSynth = _
  private var refiner: Refiner = _
  //private var solver: Solver = _
  private var ctx: LeonContext = _
  private var initialPrecondition: Expr = _
  
  private var variableRefiner: VariableRefiner = _
  // can be used to unnecessary syntheses
  private var variableRefinedBranch = false
  private var variableRefinedCondition = true // assure initial synthesis
  private var booleanExpressionsSaved: Stream[Output] = _
  
  private var seenBranchExpressions: Set[String] = Set.empty

  // flag denoting if a correct body has been synthesized
  private var found = false

  // accumulate precondition for the remaining branch to synthesize 
  private var accumulatingPrecondition: Expr = _
  // accumulate the final expression of the hole
  private var accumulatingExpression: Expr => Expr = _
  //private var accumulatingExpressionMatch: Expr => Expr = _

  // information about the synthesis
  private val synthInfo = new SynthesisInfo

  // filtering/ranking with examples support
  var exampleRunner: ExampleRunner = _

  def analyzeProgram = {
		
    synthInfo.start(Verification)
    Globals.allSolved = Some(true)

    import TreeOps._
    
    val body = holeFunDef.getBody
    val theExpr = {
	    val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val bodyAndPost = 		    
		    Let(
	    		resFresh, body,
	    		replace(Map(ResultVariable() -> LeonVariable(resFresh)), matchToIfThenElse(holeFunDef.getPostcondition))
    		)	

      val withPrec = if( holeFunDef.precondition.isEmpty) {
        bodyAndPost
      } else {
        Implies(matchToIfThenElse(holeFunDef.precondition.get), bodyAndPost)
      }

      withPrec
    }
        
    val reporter = //new DefaultReporter
      new SilentReporter
    val args =
      if (analyzeSynthesizedFunctionOnly)
        Array(fileName, "--timeout=" + leonTimeout, "--functions=" + holeFunDef.id.name)
      else
        Array(fileName, "--timeout=" + leonTimeout)
    info("Leon context array: " + args.mkString(","))
    ctx = processOptions(reporter, args.toList)
    val solver = new TimeoutSolver(new FairZ3Solver(ctx), 4000L)
      //new TimeoutSolver(synthesisContext.solver.getNewSolver, 2000L)
    solver.setProgram(program)
    
    Globals.allSolved = solver.solve(theExpr)
    fine("solver said " + Globals.allSolved + " for " + theExpr)
    //interactivePause

    // measure time
    synthInfo.end
    fine("Analysis took of theExpr: " + synthInfo.last)
  }

  // TODO return boolean (do not do unecessary analyze)
  def generateCounterexamples(program: Program, funDef: FunDef, number: Int): (Seq[Map[Identifier, Expr]], Expr) = {

    fine("generate counter examples with funDef.prec= " + funDef.precondition.getOrElse(BooleanLiteral(true)))
    
    // get current precondition
    var precondition = funDef.precondition.getOrElse(BooleanLiteral(true))
    // where we will accumulate counterexamples as sequence of maps
    var maps: Seq[Map[Identifier, Expr]] = Seq.empty

    // iterate specific number of times or until no further counterexample can be generated
    var changed = true
    var ind = 0
    while (ind < number && changed) {

      // analyze the program
      analyzeProgram

      // check if solver could solved this instance
      if (Globals.allSolved == Some(false) && !Globals.asMap.isEmpty) {

        fine("found coounterexample: " + Globals.asMap)
        // add current counterexample
        maps :+= Globals.asMap

        // prevent this counterexample to re-occur
        val precAddition = Not(And(Globals.asMap map { case (id, value) => Equals(LeonVariable(id), value) } toSeq))
        precondition = And(Seq(precondition, precAddition))
        // update precondition        
        funDef.precondition = Some(precondition)
      } else
        changed = false

      ind += 1
    }

//    val temptime = System.currentTimeMillis - temp
//    fine("Generation of counter-examples took: " + temptime)
//    verTime += temptime

    // return found counterexamples and the formed precondition
    (maps, precondition)
  }

  def getCurrentBuilder = new InitialEnvironmentBuilder(allDeclarations)

  def synthesizeBranchExpressions = {    
    synthInfo.profile(Generation) { inSynth.getExpressions(getCurrentBuilder) }    
  }

  def synthesizeBooleanExpressions = {
    synthInfo.start(Generation)
    if ( variableRefinedCondition ) {
      // store for later fetch (will memoize values)
    	booleanExpressionsSaved = 
  			inSynthBoolean.getExpressions(getCurrentBuilder).
			  filterNot(expr => refiner.isAvoidable(expr.getSnippet, problem.as)) take numberOfBooleanSnippets
			// reset flag
  		variableRefinedCondition = false
    }
  
    synthInfo end booleanExpressionsSaved
  }

  def interactivePause = {
    System.out.println("Press Any Key To Continue...");
    new java.util.Scanner(System.in).nextLine();
  }
  
  def getNewExampleQueue = PriorityQueue[(Expr, Int)]()(
    new Ordering[(Expr, Int)] {
      def compare(pair1: (Expr, Int), pair2: (Expr, Int)) =
        pair1._2.compare(pair2._2)
    })

  def initialize = {

    hole = Hole(desiredType)
    
    // TODO lose this - globals are bad
    Globals.allSolved = None

    // context needed for verification
    import leon.Main._
//    val reporter =
//      if (showLeonOutput) new DefaultReporter
//      else new SilentReporter
//
//    val args =
//      if (analyzeSynthesizedFunctionOnly)
//        Array(fileName, "--timeout=" + leonTimeout, "--functions=" + holeFunDef.id.name)
//      else
//        Array(fileName, "--timeout=" + leonTimeout)
//    info("Leon context array: " + args.mkString(","))
//    ctx = processOptions(reporter, args.toList)

    //solver = //new FairZ3Solver(ctx)
    //  new TimeoutSolver(new FairZ3Solver(ctx), leonTimeout)

    // create new insynth object
    loader = new LeonLoader(program, hole, problem.as, false)
    inSynth = new InSynth(loader, true)
    // save all declarations seen
    allDeclarations = inSynth.getCurrentBuilder.getAllDeclarations
    // make conditions synthesizer
    inSynthBoolean = new InSynth(allDeclarations, BooleanType, true)

    // funDef of the hole
    fine("postcondition is: " + holeFunDef.getPostcondition)
    fine("declarations we see: " + allDeclarations.map(_.toString).mkString("\n"))
    interactivePause

    // accumulate precondition for the remaining branch to synthesize 
    accumulatingPrecondition = holeFunDef.precondition.getOrElse(BooleanLiteral(true))
    // save initial precondition
    initialPrecondition = accumulatingPrecondition
    // accumulate the final expression of the hole
    accumulatingExpression = (finalExp: Expr) => finalExp
    //accumulatingExpressionMatch = accumulatingExpression

    // each variable of super type can actually have a subtype
    // get sine declaration maps to be able to refine them  
    variableRefiner = new VariableRefiner(loader.directSubclassesMap,
      loader.variableDeclarations, loader.classMap, reporter)

    // calculate cases that should not happen
    refiner = new Refiner(program, hole, holeFunDef)
    fine("Refiner initialized. Recursive call: " + refiner.recurentExpression)

    exampleRunner = new ExampleRunner(program, 4000)
    exampleRunner.counterExamples ++= //examples
      introduceExamples(holeFunDef.args.map(_.id), loader)
      
    fine("Introduced examples: " + exampleRunner.counterExamples.mkString(", "))
  }

  def countPassedExamples(snippet: Expr) = {
    synthInfo.start(Action.Evaluation)
    
    val oldPreconditionSaved = holeFunDef.precondition
    val oldBodySaved = holeFunDef.body

    // restore initial precondition
    holeFunDef.precondition = Some(initialPrecondition)

    // get the whole body (if else...)
    val accumulatedExpression = accumulatingExpression(snippet)
    // set appropriate body to the function for the correct evaluation
    holeFunDef.body = Some(accumulatedExpression)
    
    
    import TreeOps._
    val expressionToCheck =
      //Globals.bodyAndPostPlug(exp)
      {
		    val resFresh = FreshIdentifier("result", true).setType(accumulatedExpression.getType)		 
        Let(
          resFresh, accumulatedExpression,
          replace(Map(ResultVariable() -> LeonVariable(resFresh)), matchToIfThenElse(holeFunDef.getPostcondition)))
      }
    
    finest("going to count passed for: " + holeFunDef)
    finest("going to count passed for: " + expressionToCheck)

    val count = exampleRunner.countPassed(expressionToCheck)
//    if (snippet.toString == "Cons(l1.head, concat(l1.tail, l2))")
//      interactivePause

    holeFunDef.precondition = oldPreconditionSaved
    holeFunDef.body = oldBodySaved

    synthInfo end count
  }
  
  
  def evaluateCandidate(snippet: Expr, mapping: Map[Identifier, Expr]) = {
    
	synthInfo.start(Action.Evaluation)

    val oldPreconditionSaved = holeFunDef.precondition
    val oldBodySaved = holeFunDef.body

    // restore initial precondition
    holeFunDef.precondition = Some(initialPrecondition)

    // get the whole body (if else...)
    val accumulatedExpression = accumulatingExpression(snippet)
    // set appropriate body to the function for the correct evaluation
    holeFunDef.body = Some(accumulatedExpression)
        
    import TreeOps._
    val expressionToCheck =
      //Globals.bodyAndPostPlug(exp)
      {
		    val resFresh = FreshIdentifier("result", true).setType(accumulatedExpression.getType)		 
        Let(
          resFresh, accumulatedExpression,
          replace(Map(ResultVariable() -> LeonVariable(resFresh)), matchToIfThenElse(holeFunDef.getPostcondition)))
      }
    
    finest("going to evaluate candidate for: " + holeFunDef)
    finest("going to evaluate candidate for: " + expressionToCheck)

    val count = exampleRunner.evaluate(expressionToCheck, mapping)

    holeFunDef.precondition = oldPreconditionSaved
    holeFunDef.body = oldBodySaved

//    if(snippet.toString == "checkf(f2, reverse(r2))")
//      interactivePause
      
    synthInfo end count
  }

  def synthesize: Report = {
    reporter.info("Synthesis called on file: " + fileName)

    // profile
    synthInfo start Synthesis

    reporter.info("Initializing synthesizer: ")
    reporter.info("numberOfBooleanSnippets: %d".format(numberOfBooleanSnippets))
    reporter.info("numberOfCounterExamplesToGenerate: %d".format(numberOfCounterExamplesToGenerate))
    reporter.info("leonTimeout: %d".format(leonTimeout))
    initialize
    reporter.info("Synthesizer initialized")

    // keeps status of validity
    var keepGoing = Globals.allSolved match {
      case Some(true) => false
      case _ => true
    }
	  // update flag in case of time limit overdue
	  def checkTimeout =
	    if (synthesisContext.shouldStop.get) {
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
    var iteration = 0
    var noBranchFoundIteration = 0
    breakable {
      while (keepGoing) {
        if (checkTimeout) break
        // next iteration
        iteration += 1
        noBranchFoundIteration += 1
        reporter.info("####################################")
        reporter.info("######Iteration #" + iteration + " ###############")
        reporter.info("####################################")
        reporter.info("# precondition is: " + holeFunDef.precondition.getOrElse(BooleanLiteral(true)))
        reporter.info("# accumulatingPrecondition is: " + accumulatingPrecondition)
        reporter.info("# accumulatingExpression(Unit) is: " + accumulatingExpression(UnitLiteral))
        reporter.info("####################################")

        var numberOfTested = 0

        reporter.info("Going into a enumeration/testing phase.")
        fine("evaluating examples: " + exampleRunner.counterExamples.mkString("\n"))
                
        breakable {
          while(true) {
            val batchSize = numberOfTestsInIteration * (1 << noBranchFoundIteration)
            
          	reporter.info("numberOfTested: " + numberOfTested)
		        // ranking of candidates        
		        val candidates = {
		          val (it1, it2) = snippetsIterator.duplicate
		          snippetsIterator = it2.drop(batchSize)
		          it1.take(batchSize).        
		        	map(_.getSnippet).filterNot(
		            snip => {
		              (seenBranchExpressions contains snip.toString) || refiner.isAvoidable(snip, problem.as)
		            }
		          ).toSeq
		        }
		        info("got candidates of size: " + candidates.size)
		        //interactivePause
		        
		        // printing candidates and pass counts        
		        fine( {
		          val logString = ((candidates.zipWithIndex) map {
		            case ((snippet: Expr, ind: Int)) => ind + ": snippet is " + snippet.toString +
		              " pass count is " + countPassedExamples(snippet)
		          }).mkString("\n")
		          logString
		        })
		        //interactivePause
		          
		        if (candidates.size > 0) {
			        val ranker = new Ranker(candidates, 
			          Evaluation(exampleRunner.counterExamples, this.evaluateCandidate _, candidates, exampleRunner),
			          false)
			        
			        val maxCandidate = ranker.getMax
			        info("maxCandidate is: " + maxCandidate)
			        numberOfTested += batchSize
			        
			        if (
	        		  candidates.exists(_.toString contains "checkf(f2, Cons(x, r2))")
		            ) {
			        	println("maxCandidate is: " + maxCandidate)
			          println(ranker.printTuples)
			          println("AAA2")
			          println("Candidates: " + candidates.zipWithIndex.map({
		              case (cand, ind) => "[" + ind + "]" + cand.toString
			          }).mkString("\n"))
			          println("Examples: " + exampleRunner.counterExamples.zipWithIndex.map({
		              case (example, ind) => "[" + ind + "]" + example.toString
			          }).mkString("\n"))
			          interactivePause
			        }
			        
			        interactivePause
			        if (tryToSynthesizeBranch(maxCandidate)) {
			          noBranchFoundIteration = 0
			          break
			        }
			        interactivePause
			        
			        noBranchFoundIteration += 1
		        }
          }
        }
        
	      // add to seen if branch was not found for it
	      //seenBranchExpressions += snippetTree.toString

        // if did not found for any of the branch expressions
        if (found) {
          synthInfo end Synthesis
          reporter.info("We are done, in time: " + synthInfo.last)
          return new FullReport(holeFunDef, synthInfo)
        }

        if ( variableRefinedBranch ) {
          fine("Variable refined, doing branch synthesis again")
        	// get new snippets
        	snippets = synthesizeBranchExpressions
        	snippetsIterator = snippets.iterator
        	pq = getNewExampleQueue
        	
          // reset flag
          variableRefinedBranch = false
        } else
          // reseting iterator needed because we may have some expressions that previously did not work
        	snippetsIterator = snippets.iterator

        fine("filtering based on: " + holeFunDef.precondition.get)
        fine("counterexamples before filter: " + exampleRunner.counterExamples.size)
        exampleRunner.filter(holeFunDef.precondition.get)
        fine("counterexamples after filter: " + exampleRunner.counterExamples.size)
        fine("counterexamples after filter: " + exampleRunner.counterExamples.mkString("\n"))
      }
    } //breakable { while (!keepGoing) {

    EmptyReport
  }

  def tryToSynthesizeBranch(snippetTree: Expr): Boolean = {
    // replace hole in the body with the whole if-then-else structure, with current snippet tree
    val oldBody = holeFunDef.getBody
    val newBody = accumulatingExpression(snippetTree)
    holeFunDef.body = Some(newBody)

    // precondition
    val oldPrecondition = holeFunDef.precondition.getOrElse(BooleanLiteral(true))
    holeFunDef.precondition = Some(initialPrecondition)

    snippetTree.setType(hole.desiredType)
    //holeFunDef.getBody.setType(hole.desiredType)

    // TODO spare one analyzing step
    // analyze the program
    fine("analyzing program for funDef:" + holeFunDef)
//    solver.setProgram(program)
    analyzeProgram

    // check if solver could solved this instance
    if (Globals.allSolved == Some(true)) {
      // mark the branch found
      found = true

      reporter.info("Wooooooow we have a winner!")
      reporter.info("************************************")
      reporter.info("*********And the winner is**********")
      reporter.info(accumulatingExpression(snippetTree).toString)
      reporter.info("************************************")

      return true
    }

    // store appropriate values here, will be update in a finally branch
    var bodyToRestore = oldBody
    var preconditionToRestore = Some(oldPrecondition)

    // because first initial test
    holeFunDef.precondition = preconditionToRestore

    // get counterexamples
    fine("Going to generating counterexamples: " + holeFunDef)
    val (maps, precondition) = generateCounterexamples(program, holeFunDef, numberOfCounterExamplesToGenerate)

    // collect (add) counterexamples from leon
    if (collectCounterExamplesFromLeon)
      exampleRunner.counterExamples ++= maps

    // this should not be possible
    //    val keepGoing = Globals.allSolved match {
    //      case Some(true) => false
    //      case _ => true
    //    }
    //
    //    // if no counterexamples and all are solved, we are done
    //    if (maps.isEmpty && !keepGoing) {
    //      // mark the branch found
    //      found = true
    //
    //      println("Wooooooow we have a winner!")
    //      println("************************************")
    //      println("*********And the winner is**********")
    //      println(accumulatingExpression(snippetTree))
    //      println("************************************")
    //
    //      return true
    //    }

      //if(maps.isEmpty) throw new RuntimeException("asdasdasd")


      
    // will modify funDef body and precondition, restore it later
    try {
      { //if (!maps.isEmpty) {
        // proceed with synthesizing boolean expressions
        solver.setProgram(program)

        // reconstruct (only defined number of boolean expressions)
        val innerSnippets = synthesizeBooleanExpressions
        // just printing of expressions
        fine(
          ((innerSnippets zip Iterator.range(0, numberOfBooleanSnippets).toStream) map {
            case ((snippet: Output, ind: Int)) => ind + ": snippet is " + snippet.getSnippet
          }).mkString("\n"))

        for (
            innerSnippetTree <- innerSnippets map { _.getSnippet };
            if (
              {	val flag = !refiner.isAvoidable(innerSnippetTree, problem.as)
                if (!flag) fine("Refiner filtered this snippet: " + innerSnippetTree)
                flag }
            )
          ) {
          fine("boolean snippet is: " + innerSnippetTree)

          val (innerFound, innerPrec) = tryToSynthesizeBooleanCondition(snippetTree, innerSnippetTree, precondition)

          // if precondition found
          if (innerFound) {
            reporter.info("Precondition " + innerPrec + " found for " + snippetTree)

            innerPrec match {
              case s @ Some(_) =>
                // new precondition (restore in finally)
                preconditionToRestore = s
              case _ =>
            }
            return true
          }

        } // iterating over all boolean solutions

        reporter.info("No precondition found for branch expression: " + snippetTree)
        return false

      } // if ( !maps.isEmpty ) {
      // no counter examples, we just say that we cannot do anything
      false
    } // try
    finally {
      // set these to the FunDef
      holeFunDef.precondition = preconditionToRestore
      // restore old body (we accumulate expression)                                
      holeFunDef.body = Some(oldBody)
    }
  }

  def tryToSynthesizeBooleanCondition(snippetTree: Expr, innerSnippetTree: Expr, precondition: Expr): (Boolean, Option[Expr]) = {
		
    // new condition together with existing precondition
    val newCondition = And(Seq(accumulatingPrecondition, innerSnippetTree))

    // new expression should not be false
    val notFalseEquivalence = Not(newCondition)
    val notFalseSolveReturn = solver.solve(notFalseEquivalence)
    fine("solve for not false returned: " + notFalseSolveReturn)

    notFalseSolveReturn match {
      case Some(true) =>
        (false, None)
      case None =>
        (false, None)
      // nothing here
      // here, our expression is not contradictory, continue
      case Some(false) =>
        // check if synthesized boolean expression implies precondition (counterexamples)
        val implyExpression = Implies(newCondition, precondition)
        fine("implyExpression is: " + implyExpression)

        // check if synthesized condition implies counter-examples
        val solveReturn = solver.solve(implyExpression)
        fine("solve returned: " + solveReturn)

        solveReturn match {
          case Some(true) =>
            // if expression implies counterexamples add it to the precondition and try to validate program
            holeFunDef.precondition = Some(newCondition)
            // do analysis
//            solver.setProgram(program)
            analyzeProgram
            // program is valid, we have a branch
            if (Globals.allSolved == Some(true)) {
              // we found a branch
              reporter.info("We found a branch, for expression %s, with condition %s.".format(snippetTree, innerSnippetTree))

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
              accumulatingPrecondition = And(Seq(accumulatingPrecondition, Not(innerSnippetTree)))
              fine("updating hole fun precondition and body (to be hole)")

              // set to set new precondition
              val preconditionToRestore = Some(accumulatingPrecondition)

              val variableRefinementResult = variableRefiner.checkRefinements(innerSnippetTree, allDeclarations)
              if (variableRefinementResult._1) {
                allDeclarations = variableRefinementResult._2
                
              	// the reason for two flags is for easier management of re-syntheses only if needed 
                variableRefinedBranch = true
            		variableRefinedCondition = true
              }
              
              // found a boolean snippet, break
              (true, preconditionToRestore)
            } else {
              // reset funDef and continue with next boolean snippet
              val preconditionToRestore = Some(accumulatingPrecondition)
              (false, preconditionToRestore)
            }

          case _ =>

            fine("solver filtered out the precondition (does not imply counterexamples)")
            (false, None)
        } //solveReturn match { (for implying counterexamples)
    } // notFalseSolveReturn match {
  }

}