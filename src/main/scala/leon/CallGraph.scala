package leon

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Common._

class CallGraph(val program: Program) {

  sealed abstract class ProgramPoint
  case class FunctionStart(fd: FunDef) extends ProgramPoint
  case class ExpressionPoint(wp: Expr) extends ProgramPoint

  sealed abstract class EdgeLabel
  case class ConditionLabel(expr: Expr) extends EdgeLabel {
    require(expr.getType == BooleanType)
  }
  case class FunctionInvocLabel(fd: FunDef, args: List[Expr]) extends EdgeLabel {
    require(args.zip(fd.args).forall(p => p._1.getType == p._2.getType))
  }

  private lazy val graph: Map[ProgramPoint, Set[EdgeLabel]] = buildGraph


  private def buildGraph: Map[ProgramPoint, Set[EdgeLabel]] = {
    null
  }

//  def hoistIte(expr: Expr): Expr = expr match {
//    case ite@IfExpr(c, t, e) => IfExpr(c, hoistIte(t), hoistIte(e)).setType(ite.getType)
//    case BinaryOperator(t1, t2) =>
//
//  }

  //def analyse(program: Program) {
  //  z3Solver.setProgram(program)
  //  reporter.info("Running test generation")
  //  val allFuns = program.definedFunctions
  //  allFuns.foreach(fd => {
  //    val testcases = generateTestCases(fd)
  //    reporter.info("Running " + fd.id + " with the following testcases:\n")
  //    reporter.info(testcases.mkString("\n"))
  //  })
  //}

  //private def generatePathConditions(funDef: FunDef): Seq[Expr] = if(!funDef.hasImplementation) Seq() else {
  //  val body = funDef.body.get
  //  val cleanBody = expandLets(matchToIfThenElse(body))
  //  collectWithPathCondition(cleanBody)
  //}

  //// prec: there should be no lets and no pattern-matching in this expression
  //  private def collectWithPathCondition(expression: Expr): Seq[Expr] = {
  //  var allPaths: Seq[Expr] = Seq()

  //  def rec(expr: Expr, path: Expr): Seq[Expr] = expr match {
  //    case IfExpr(cond, then, elze) =>
  //      (if(!containsIfExpr(then)) Seq(And(path, cond)) else rec(then, And(cond, path))) ++
  //      (if(!containsIfExpr(elze)) Seq(And(path, Not(cond))) else rec(then, And(cond, path)))
  //    case NAryOperator(args, _) => args.flatMap(arg => rec(arg, path))
  //    case BinaryOperator(t1, t2, _) => rec(t1, path) ++ rec(t2, path)
  //    case UnaryOperator(t, _) => rec(t, path)
  //    case t : Terminal => Seq()
  //    case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
  //  }

  //  rec(expression, BooleanLiteral(true)).distinct
  //}
}
