package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import Extensions._
import scala.collection.mutable.{Set => MutableSet}


class TestGeneration(reporter: Reporter) extends Analyser(reporter) {

  def description: String = "Generate random testcases"
  override def shortDescription: String = "test"


  def analyse(program: Program) {
    reporter.info("Running test generation")
    val allFuns = program.definedFunctions
    allFuns.foreach(generateTestCases)
  }

  private def generatePathConditions(funDef: FunDef): Seq[Expr] = if(!funDef.hasImplementation) Seq() else {
    val body = funDef.body.get
    val cleanBody = expandLets(matchToIfThenElse(body))
    collectWithPathCondition(cleanBody)
  }

  private def generateTestCases(funDef: FunDef): Seq[Expr] = {
    val allPaths = generatePathConditions(funDef)

    allPaths.map(pathCond => {
      reporter.info("Now considering path condition: " + pathCond)

      // try all solvers until one returns a meaningful answer
      var testcase: Option[Expr] = None
      val solverExtensions: Seq[Solver] = loadedSolverExtensions
      solverExtensions.find(se => {
        reporter.info("Trying with solver: " + se.shortDescription)
        val t1 = System.nanoTime
        se.init()
        val solverResult = se.solve(Not(pathCond))
        val t2 = System.nanoTime
        val dt = ((t2 - t1) / 1000000) / 1000.0

        solverResult match {
          case None => false
          case Some(true) => {
            reporter.info("==== VALID ====")
            reporter.info("This means the path is unreachable")
            testcase = None
            true
          }
          case Some(false) => {
            reporter.info("==== INVALID ====")
            reporter.info("The model should be used as the testcase")
            testcase = None
            true
          }
        }
      })
      null
    })
  }

  // prec: there should be no lets and no pattern-matching in this expression
    private def collectWithPathCondition(expression: Expr): Seq[Expr] = {
    var allPaths: Seq[Expr] = Seq()

    def rec(expr: Expr, path: Expr): Seq[Expr] = expr match {
      case IfExpr(cond, then, elze) =>
        (if(!containsIfExpr(then)) Seq(And(path, cond)) else rec(then, And(cond, path))) ++
        (if(!containsIfExpr(elze)) Seq(And(path, Not(cond))) else rec(then, And(cond, path)))
      case NAryOperator(args, _) => args.flatMap(arg => rec(arg, path))
      case BinaryOperator(t1, t2, _) => rec(t1, path) ++ rec(t2, path)
      case UnaryOperator(t, _) => rec(t, path)
      case t : Terminal => Seq()
      case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
    }

    rec(expression, BooleanLiteral(true)).distinct
  }

}



