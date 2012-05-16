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

  private val z3Solver = new FairZ3Solver(reporter)

  def analyse(program: Program) {
    val callGraph = new CallGraph(program)
    callGraph.writeDotFile("testgen.dot")
    callGraph.findAllPathes.foreach(path => {
      println("Path is: " + path)
      println("constraint is: " + callGraph.pathConstraint(path))
    })
    //z3Solver.setProgram(program)
    //reporter.info("Running test generation")
    //val allFuns = program.definedFunctions
    //allFuns.foreach(fd => {
    //  val testcases = generateTestCases(fd)
    //  reporter.info("Running " + fd.id + " with the following testcases:\n")
    //  reporter.info(testcases.mkString("\n"))
    //})
  }

  private def generatePathConditions(funDef: FunDef): Seq[Expr] = if(!funDef.hasImplementation) Seq() else {
    val body = funDef.body.get
    val cleanBody = expandLets(matchToIfThenElse(body))
    collectWithPathCondition(cleanBody)
  }

  private def generateTestCases(funDef: FunDef): Seq[Map[Identifier, Expr]] = {
    val allPaths = generatePathConditions(funDef)

    allPaths.flatMap(pathCond => {
      reporter.info("Now considering path condition: " + pathCond)

      var testcase: Option[Map[Identifier, Expr]] = None
      //val z3Solver: FairZ3Solver = loadedSolverExtensions.find(se => se.isInstanceOf[FairZ3Solver]).get.asInstanceOf[FairZ3Solver]
        
      z3Solver.init()
      z3Solver.restartZ3
      val (solverResult, model) = z3Solver.decideWithModel(pathCond, false)

      solverResult match {
        case None => Seq()
        case Some(true) => {
          reporter.info("The path is unreachable")
          Seq()
        }
        case Some(false) => {
          reporter.info("The model should be used as the testcase")
          Seq(model)
        }
      }
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



