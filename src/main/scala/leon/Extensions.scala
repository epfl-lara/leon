package leon

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._

object Extensions {
  sealed abstract class Extension(reporter: Reporter) {
    def description: String
    def shortDescription: String = description
  }

  abstract class Solver(val reporter: Reporter) extends Extension(reporter) {
    // This can be used by solvers to "see" the programs from which the
    // formulas come. (e.g. to set up some datastructures for the defined
    // ADTs, etc.) 
    def setProgram(program: Program) : Unit = {}

    // Returns Some(true) if valid, Some(false) if invalid,
    // None if unknown.
    // should halt as soon as possible with any result (Unknown is ok) as soon as forceStop is true
    def solve(expression: Expr) : Option[Boolean]

    def solveOrGetCounterexample(expression : Expr) : (Option[Boolean],Map[Identifier,Expr]) = (solve(expression), Map.empty)

    def isUnsat(expression: Expr) : Option[Boolean] = solve(negate(expression))
    def superseeds : Seq[String] = Nil

    private var _forceStop = false
    def halt() : Unit = {
      _forceStop = true
    }
    def init() : Unit = {
      _forceStop = false
    }
    protected def forceStop = _forceStop

  }
  
  abstract class Analyser(reporter: Reporter) extends Extension(reporter) {
    // Does whatever the analysis should. Uses the reporter to
    // signal results and/or errors.
    def analyse(program: Program) : Unit
  }

  abstract class Tactic(reporter: Reporter) extends Extension(reporter) {
    def setProgram(program: Program) : Unit = {}
    def generatePostconditions(function: FunDef) : Seq[VerificationCondition]
    def generatePreconditions(function: FunDef) : Seq[VerificationCondition]
    def generatePatternMatchingExhaustivenessChecks(function: FunDef) : Seq[VerificationCondition]
    def generateMiscCorrectnessConditions(function: FunDef) : Seq[VerificationCondition]
    def generateArrayAccessChecks(function: FunDef) : Seq[VerificationCondition]
  }

  // The rest of the code is for dynamically loading extensions

  private var allLoaded : Seq[Extension] = Nil
  private var analysisExtensions : Seq[Analyser] = Nil
  private var solverExtensions : Seq[Solver] = Nil

  // Returns the list of the newly loaded.
  def loadAll(extensionsReporter : Reporter = Settings.reporter) : Seq[Extension] = {
    val allNames: Seq[String] = Settings.extensionNames
    val loaded = (if(!allNames.isEmpty) {
      val classLoader = Extensions.getClass.getClassLoader

      val classes: Seq[Class[_]] = (for(name <- allNames) yield {
        try {
          classLoader.loadClass(name)
        } catch {
          case _ => {
            Settings.reporter.error("Couldn't load extension class " + name) 
            null
          }
        }
      }).filter(_ != null)

      classes.map(cl => {
        try {
          val cons = cl.getConstructor(classOf[Reporter])
          cons.newInstance(extensionsReporter).asInstanceOf[Extension]
        } catch {
          case _ => {
            Settings.reporter.error("Extension class " + cl.getName + " does not seem to be of a proper type.")
            null
          }
        }
      }).filter(_ != null)
    } else {
      Nil
    })
    if(!loaded.isEmpty) {
      Settings.reporter.info("The following extensions are loaded:\n" + loaded.toList.map(_.description).mkString("  ", "\n  ", ""))
    }
    // these extensions are always loaded, unless specified otherwise
    val defaultExtensions: Seq[Extension] = if(Settings.runDefaultExtensions) {
      val z3 : Solver = new FairZ3Solver(extensionsReporter)
      z3 :: Nil
    } else {
      Nil
    }

    allLoaded = defaultExtensions ++ loaded
    analysisExtensions = allLoaded.filter(_.isInstanceOf[Analyser]).map(_.asInstanceOf[Analyser])
    //analysisExtensions = new TestGeneration(extensionsReporter) +: analysisExtensions

    val solverExtensions0 = allLoaded.filter(_.isInstanceOf[Solver]).map(_.asInstanceOf[Solver])
    val solverExtensions1 = if(Settings.useQuickCheck) new RandomSolver(extensionsReporter) +: solverExtensions0 else solverExtensions0
    val solverExtensions2 = if(Settings.useParallel) Seq(new ParallelSolver(solverExtensions1: _*)) else solverExtensions1
    val solverExtensions3 = 
      if(Settings.solverTimeout == None) {
        solverExtensions2 
      } else {
        val t = Settings.solverTimeout.get 
        solverExtensions2.map(s => new TimeoutSolver(s, t))
      }
    solverExtensions = solverExtensions3
    loaded
  }

  def loadedExtensions : Seq[Extension] = allLoaded
  def loadedAnalysisExtensions : Seq[Analyser] = analysisExtensions
  def loadedSolverExtensions : Seq[Solver] = solverExtensions
}
