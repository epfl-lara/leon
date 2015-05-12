package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.utils._
import leon.invariant.util.Util._

object timeCostModel {
  def costOf(e: Expr): Int = e match {
    case FunctionInvocation(fd, args) => 1
    case t: Terminal => 0
    case _ => 1
  }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}

class TimeInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  import timeCostModel._

  def inst = Time

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
    val instFunSet = getRootFuncs().foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))
    instFunSet.map(x => (x, List(Time))).toMap
  }

  def additionalfunctionsToAdd() = Seq()

  def instrumentMatchCase(
    me: MatchExpr,
    mc: MatchCase,
    caseExprCost: Expr,
    scrutineeCost: Expr): Expr = {
    val costMatch = costOfExpr(me)

    def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = {

      def patCostRecur(pattern: Pattern, innerPat: Boolean, countLeafs: Boolean): Int = {
        pattern match {
          case InstanceOfPattern(_, _) => {
            if (innerPat) 2 else 1
          }
          case WildcardPattern(None) => 0
          case WildcardPattern(Some(id)) => {
            if (countLeafs && innerPat) 1
            else 0
          }
          case CaseClassPattern(_, _, subPatterns) => {
            (if (innerPat) 2 else 1) + subPatterns.foldLeft(0)((acc, subPat) =>
              acc + patCostRecur(subPat, true, countLeafs))
          }
          case TuplePattern(_, subPatterns) => {
            (if (innerPat) 2 else 1) + subPatterns.foldLeft(0)((acc, subPat) =>
              acc + patCostRecur(subPat, true, countLeafs))
          }
          case LiteralPattern(_, _) => if (innerPat) 2 else 1
          case _ =>
            throw new NotImplementedError(s"Pattern $pattern not handled yet!")
        }
      }

      me.cases.take(me.cases.indexOf(mc)).foldLeft(0)(
        (acc, currCase) => acc + patCostRecur(currCase.pattern, false, false)) +
        patCostRecur(mc.pattern, false, true)
    }

    Plus(costMatch, Plus(
      Plus(InfiniteIntegerLiteral(totalCostOfMatchPatterns(me, mc)),
        caseExprCost),
      scrutineeCost))
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
  	(implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    case t: Terminal => costOfExpr(t)
    case _ =>
      subInsts.foldLeft(costOfExpr(e) : Expr)(
        (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {
    val costIf = costOfExpr(e)
    (Plus(costIf, Plus(condInst.get, thenInst.get)),
      Plus(costIf, Plus(condInst.get, elzeInst.get)))
  }
}