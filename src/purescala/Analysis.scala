package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._
import Extensions._
import scala.collection.mutable.{Set => MutableSet}

class Analysis(val program: Program) {
  // we always use the global reporter for this class
  val reporter = Settings.reporter
  // ...but not always for the extensions

  Extensions.loadAll

  val analysisExtensions: Seq[Analyser] = loadedAnalysisExtensions

  val trivialSolver = new TrivialSolver(reporter) // This one you can't disable :D
  val solverExtensions: Seq[Solver] = trivialSolver +: loadedSolverExtensions
  solverExtensions.foreach(_.setProgram(program))

  val defaultTactic = new DefaultTactic(reporter)
  defaultTactic.setProgram(program)
  val inductionTactic = new InductionTactic(reporter)
  inductionTactic.setProgram(program)

  // Calling this method will run all analyses on the program passed at
  // construction time. If at least one solver is loaded, verification
  // conditions are generated and passed to all solvers. Otherwise, only the
  // Analysis extensions are run on the program.
  def analyse : Unit = {
    if(solverExtensions.size > 0) {
      reporter.info("Running verification condition generation...")

      val list = generateVerificationConditions
      checkVerificationConditions(list : _*)
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
    }

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })
  }

  private def generateVerificationConditions : List[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty
    val analysedFunctions: MutableSet[String] = MutableSet.empty

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name))) {
      analysedFunctions += funDef.id.name

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      def vcSort(vc1: VerificationCondition, vc2: VerificationCondition) : Boolean = (vc1 < vc2)

      if(funDef.body.isDefined) {
        allVCs ++= tactic.generatePreconditions(funDef).sortWith(vcSort)
        allVCs ++= tactic.generatePatternMatchingExhaustivenessChecks(funDef).sortWith(vcSort)
        allVCs ++= tactic.generatePostconditions(funDef).sortWith(vcSort)
        allVCs ++= tactic.generateMiscCorrectnessConditions(funDef).sortWith(vcSort)
      }
    }

    val notFound: Set[String] = Settings.functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))

    allVCs.toList
  }

  def checkVerificationCondition(vc: VerificationCondition) : Unit = checkVerificationConditions(vc)
  def checkVerificationConditions(vcs: VerificationCondition*) : Unit = {
    for(vcInfo <- vcs) {
      val funDef = vcInfo.funDef
      val vc = vcInfo.condition

      reporter.info("Now considering '" + vcInfo.kind + "' VC for " + funDef.id + "...")
      // reporter.info("Verification condition (post) for ==== " + funDef.id + " ====")
      // if(Settings.unrollingLevel == 0) {
      //   reporter.info(simplifyLets(vc))
      // } else {
      //   reporter.info("(not showing unrolled VCs)")
      // }

      // try all solvers until one returns a meaningful answer
      var superseeded : Set[String] = Set.empty[String]
      solverExtensions.find(se => {
        reporter.info("Trying with solver: " + se.shortDescription)
        if(superseeded(se.shortDescription) || superseeded(se.description)) {
          reporter.info("Solver was superseeded. Skipping.")
          false
        } else {
          superseeded = superseeded ++ Set(se.superseeds: _*)

          val t1 = System.nanoTime
          val solverResult = se.solve(vc)
          val t2 = System.nanoTime
          val dt = ((t2 - t1) / 1000000) / 1000.0

          solverResult match {
            case None => false
            case Some(true) => {
              reporter.info("==== VALID ====")

              vcInfo.value = Some(true)
              vcInfo.solvedWith = Some(se)
              vcInfo.time = Some(dt)

              true
            }
            case Some(false) => {
              reporter.error("==== INVALID ====")

              vcInfo.value = Some(false)
              vcInfo.solvedWith = Some(se)
              vcInfo.time = Some(dt)

              true
            }
          }
        }
      }) match {
        case None => {
          reporter.warning("No solver could prove or disprove the verification condition.")
        }
        case _ => 
      } 
    
    } 

    if(vcs.size > 0) {
      val summaryString = (
        VerificationCondition.infoHeader +
        vcs.map(_.infoLine).mkString("\n", "\n", "\n") +
        VerificationCondition.infoFooter
      )
      reporter.info(summaryString)
    } else {
      reporter.info("No verification conditions were analyzed.")
    }
  }
}

object Analysis {
  private val keepCallWhenInlined: Boolean = true

  private def defineOneInlining(f : FunctionInvocation) : (Expr, Expr) = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(matchToIfThenElse(fd.body.get)))
    val newFunctionCall = FunctionInvocation(fd, newLetIDs.map(Variable(_))).setType(f.getType)
    val callID = FreshIdentifier("call_" + fd.id.name, true).setType(newBody.getType)
    val callTree = Let(callID, (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e)), Variable(callID))

    (Equals(newFunctionCall, Variable(callID)), callTree)
  }

  private def inlineFunctionCall(f : FunctionInvocation) : Expr = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(matchToIfThenElse(fd.body.get)))
    simplifyLets((newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e)))
  }

  def inlineNonRecursiveFunctions(program: Program, expression: Expr) : Expr = {
    def applyToCall(e: Expr) : Option[Expr] = e match {
      case f @ FunctionInvocation(fd, args) if fd.hasImplementation && !program.isRecursive(fd) => Some(inlineFunctionCall(f))
      case _ => None
    }
  
    var change: Boolean = true
    var toReturn: Expr = expression
    while(change) {
      val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
      change = c
      toReturn = t
    }
    toReturn
  }

  def unrollRecursiveFunctions(program: Program, expression: Expr, times: Int) : Expr = {
    def urf1(expression: Expr, times: Int) : Expr = {
      var newEqs: List[Expr] = Nil

      def applyToCall(e: Expr) : Option[Expr] = e match {
        case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => {
          val (newEq, bdy) = defineOneInlining(f)
          newEqs = newEq :: newEqs
          Some(bdy)
        }
        case _ => None
      }

      var remaining = if(times < 0) 0 else times
      var change: Boolean = true
      var toReturn: Expr = expression
      while(remaining > 0 && change) {
        val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
        change = c
        toReturn = inlineNonRecursiveFunctions(program, t)
        remaining = remaining - 1
      }
      liftLets(Implies(And(newEqs.reverse), toReturn))
    }

    def urf2(expression: Expr, times: Int) : Expr = {
      def applyToCall(e: Expr) : Option[Expr] = e match {
        case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => Some(inlineFunctionCall(f))
        case _ => None
      }

      var remaining = if(times < 0) 0 else times
      var change: Boolean = true
      var toReturn: Expr = expression
      while(remaining > 0 && change) {
        val (t,c) = searchAndReplaceDFSandTrackChanges(applyToCall)(toReturn)
        change = c
        toReturn = inlineNonRecursiveFunctions(program, t)
        remaining = remaining - 1
      }
      toReturn
    }

    if(keepCallWhenInlined)
      urf1(expression, times)
    else
      urf2(expression, times)
  }

  def inlineContracts(expression: Expr) : Expr = {
    var trueThings: List[Expr] = Nil

    def applyToCall(e: Expr) : Option[Expr] = e match {
      case f @ FunctionInvocation(fd, args) if fd.hasPostcondition => {
        val argsAsLet   = fd.args.map(a => FreshIdentifier("parg_" + a.id.name, true).setType(a.tpe)).toList
        val argsAsLetVars = argsAsLet.map(Variable(_))
        val resultAsLet = FreshIdentifier("call_" + fd.id.name, true).setType(f.getType)
        val newFunCall = FunctionInvocation(fd, argsAsLetVars)
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip argsAsLetVars) : _*) + (ResultVariable() -> Variable(resultAsLet))
        // this thing is full of let variables! We will need to lift the let
        // defs. later to make sure they capture this
        val trueFact = replace(substMap, freshenLocals(fd.postcondition.get))
        val defList: Seq[(Identifier,Expr)] = ((argsAsLet :+ resultAsLet) zip (args :+ newFunCall))
        trueThings = trueFact :: trueThings
        // again: these let defs. need eventually to capture the "true thing"
        Some(defList.foldRight[Expr](Variable(resultAsLet))((iap, e) => Let(iap._1, iap._2, e)))
      }
      case _ => None
    }
    val result = searchAndReplaceDFS(applyToCall)(expression)
    liftLets(Implies(And(trueThings.reverse), result))
  }

  // Rewrites pattern matching expressions where the cases simply correspond to
  // the list of constructors
  // def rewriteSimplePatternMatching(expression: Expr) : Expr = {
  //   var extras : List[Expr] = Nil

  //   def rewritePM(e: Expr) : Option[Expr] = e match {
  //     // case NotSoSimplePatternMatching(_) => None
  //     case SimplePatternMatching(scrutinee, classType, casesInfo) => {
  //       val newVar = Variable(FreshIdentifier("pm", true)).setType(e.getType)
  //       val scrutAsLetID = FreshIdentifier("scrut", true).setType(scrutinee.getType)
  //       val lle : List[(Variable,List[Expr])] = casesInfo.map(cseInfo => {
  //         val (ccd, newPID, argIDs, rhs) = cseInfo
  //         val newPVar = Variable(newPID)
  //         val argVars = argIDs.map(Variable(_))
  //         (newPVar, List(Equals(newPVar, CaseClass(ccd, argVars)), Implies(Equals(Variable(scrutAsLetID), newPVar), Equals(newVar, rhs))))
  //       }).toList
  //       val (newPVars, newExtras) = lle.unzip
  //       extras = Let(scrutAsLetID, scrutinee, And(Or(newPVars.map(Equals(Variable(scrutAsLetID), _))), And(newExtras.flatten))) :: extras 
  //       Some(newVar)
  //     }
  //     case m @ MatchExpr(s,_) => Settings.reporter.error("Untranslatable PM expression on type " + s.getType + " : " + m); None
  //     case _ => None
  //   }

  //   val newExpr = searchAndReplaceDFS(rewritePM)(expression)
  //   liftLets(Implies(And(extras), newExpr))
  // }
}
