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


}
