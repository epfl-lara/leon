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
  val solverExtensions: Seq[Solver] = loadedSolverExtensions

  val trivialSolver = new Solver(reporter) {
    val description = "Trivial"
    override val shortDescription = "trivial"
    def solve(e: Expr) = throw new Exception("trivial solver should not be called.")
  }

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
      // checkVerificationConditions

      val list = generateVerificationConditions
      list.foreach(e => println(e.infoLine))
    } else {
      reporter.warning("No solver specified. Cannot test verification conditions.")
    }

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })
  }

  def generateVerificationConditions : List[VerificationCondition] = {
    var allVCs: Seq[VerificationCondition] = Seq.empty

    for(funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1.id.name < fd2.id.name) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name))) {
      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        allVCs ++= tactic.generatePreconditions(funDef)
        allVCs ++= tactic.generatePostconditions(funDef)
        allVCs ++= tactic.generatePatternMatchingExhaustivenessChecks(funDef)
        allVCs ++= tactic.generateMiscCorrectnessConditions(funDef)
      }
    }

    allVCs.toList
  }

  def checkVerificationConditions : Unit = {
    // just for the summary:
    var verificationConditionInfos: List[VerificationCondition] = Nil

    var analysedFunctions: MutableSet[String] = MutableSet.empty

    solverExtensions.foreach(_.setProgram(program))

    for(funDef <- program.definedFunctions.toList.sortWith((fd1,fd2) => fd1.id.name < fd2.id.name)) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name)) {
      analysedFunctions += funDef.id.name
      if(funDef.body.isDefined) {
        val vcInfo = defaultTactic.generatePostconditions(funDef).head
        val vc = vcInfo.condition
        // val vc = postconditionVC(funDef)
        // val vcInfo = new VerificationCondition(vc, funDef, VCKind.Postcondition, defaultTactic)
        verificationConditionInfos = vcInfo :: verificationConditionInfos

        if(vc == BooleanLiteral(false)) {
          vcInfo.value = Some(false)
          vcInfo.solvedWith = Some(trivialSolver)
          vcInfo.time = Some(0L)
        } else if(vc == BooleanLiteral(true)) {
          if(funDef.hasPostcondition) {
          vcInfo.value = Some(true)
          vcInfo.solvedWith = Some(trivialSolver)
          vcInfo.time = Some(0L)
          }
        } else {
          reporter.info("Verification condition (post) for ==== " + funDef.id + " ====")
          if(true || Settings.unrollingLevel == 0) {
            reporter.info(simplifyLets(vc))
          } else {
            reporter.info("(not showing unrolled VCs)")
          }

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
      } else {
        if(funDef.postcondition.isDefined) {
          reporter.warning(funDef, "Could not verify postcondition: function implementation is unknown.")
        }
      }
    } 

    if(verificationConditionInfos.size > 0) {
      verificationConditionInfos = verificationConditionInfos.reverse
      val summaryString = (
        VerificationCondition.infoHeader +
        verificationConditionInfos.map(_.infoLine).mkString("\n", "\n", "\n") +
        VerificationCondition.infoFooter
      )
      reporter.info(summaryString)
    } else {
      reporter.info("No verification conditions were generated.")
    }

    val notFound: Set[String] = Settings.functionsToAnalyse -- analysedFunctions
    notFound.foreach(fn => reporter.error("Did not find function \"" + fn + "\" though it was marked for analysis."))
  }

  def postconditionVC(functionDefinition: FunDef) : Expr = {
    assert(functionDefinition.body.isDefined)
    val prec = functionDefinition.precondition
    val post = functionDefinition.postcondition
    val body = functionDefinition.body.get

    if(post.isEmpty) {
      BooleanLiteral(true)
    } else {
      val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val bodyAndPost = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), post.get))
      val withPrec = if(prec.isEmpty) {
        bodyAndPost
      } else {
        Implies(prec.get, bodyAndPost)
      }

      import Analysis._
    
      if(Settings.experimental) {
        reporter.info("Raw:")
        reporter.info(withPrec)
        reporter.info("Raw, expanded:")
        reporter.info(expandLets(withPrec))
      }
      reporter.info(" - inlining...")
      val expr0 = inlineNonRecursiveFunctions(program, withPrec)
      if(Settings.experimental) {
        reporter.info("Inlined:")
        reporter.info(expr0)
        reporter.info("Inlined, expanded:")
        reporter.info(expandLets(expr0))
      }
      reporter.info(" - unrolling...")
      val expr1 = unrollRecursiveFunctions(program, expr0, Settings.unrollingLevel)
      if(Settings.experimental) {
        reporter.info("Unrolled:")
        reporter.info(expr1)
        reporter.info("Unrolled, expanded:")
        reporter.info(expandLets(expr1))
      }
      reporter.info(" - inlining contracts...")
      val expr2 = inlineContracts(expr1)
      if(Settings.experimental) {
        reporter.info("Contract'ed:")
        reporter.info(expr2)
        reporter.info("Contract'ed, expanded:")
        reporter.info(expandLets(expr2))
      }
      reporter.info(" - converting pattern-matching...")
      val expr3 = rewriteSimplePatternMatching(expr2)
      if(Settings.experimental) {
        reporter.info("Pattern'ed:")
        reporter.info(expr3)
        reporter.info("Pattern'ed, expanded:")
        reporter.info(expandLets(expr3))
      }
      expr3
    }
  }
}

object Analysis {
  private val keepCallWhenInlined: Boolean = true

  private def defineOneInlining(f : FunctionInvocation) : (Expr, Expr) = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(fd.body.get))
    val newFunctionCall = FunctionInvocation(fd, newLetIDs.map(Variable(_))).setType(f.getType)
    val callID = FreshIdentifier("call_" + fd.id.name, true).setType(newBody.getType)
    val callTree = Let(callID, (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e)), Variable(callID))

    (Equals(newFunctionCall, Variable(callID)), callTree)
  }

  private def inlineFunctionCall(f : FunctionInvocation) : Expr = {
    val FunctionInvocation(fd, args) = f
    val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe)).toList
    val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
    val newBody = replace(substMap, freshenLocals(fd.body.get))
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
  def rewriteSimplePatternMatching(expression: Expr) : Expr = {
    var extras : List[Expr] = Nil

    def rewritePM(e: Expr) : Option[Expr] = e match {
      // case NotSoSimplePatternMatching(_) => None
      case SimplePatternMatching(scrutinee, classType, casesInfo) => {
        val newVar = Variable(FreshIdentifier("pm", true)).setType(e.getType)
        val scrutAsLetID = FreshIdentifier("scrut", true).setType(scrutinee.getType)
        val lle : List[(Variable,List[Expr])] = casesInfo.map(cseInfo => {
          val (ccd, newPID, argIDs, rhs) = cseInfo
          val newPVar = Variable(newPID)
          val argVars = argIDs.map(Variable(_))
          (newPVar, List(Equals(newPVar, CaseClass(ccd, argVars)), Implies(Equals(Variable(scrutAsLetID), newPVar), Equals(newVar, rhs))))
        }).toList
        val (newPVars, newExtras) = lle.unzip
        extras = Let(scrutAsLetID, scrutinee, And(Or(newPVars.map(Equals(Variable(scrutAsLetID), _))), And(newExtras.flatten))) :: extras 
        Some(newVar)
      }
      case m @ MatchExpr(s,_) => Settings.reporter.error("Untranslatable PM expression on type " + s.getType + " : " + m); None
      case _ => None
    }

    val newExpr = searchAndReplaceDFS(rewritePM)(expression)
    liftLets(Implies(And(extras), newExpr))
  }
}
