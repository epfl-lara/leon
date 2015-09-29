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

import scala.collection.mutable.{Map => MutableMap}

object tprCostModel {
  def costOf(e: Expr): Int = e match {
    case FunctionInvocation(fd, args) => 1
    case t: Terminal => 0
    case _ => 1
  }
  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}

class TPRInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  import tprCostModel._

  def inst = TPR

  val sccs = cg.graph.sccs.flatMap { scc =>
    scc.map(fd => (fd -> scc.toSet))
  }.toMap

  //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
  val tprFuncs = getRootFuncs()
  val timeFuncs = tprFuncs.foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    var emap = MutableMap[FunDef,List[Instrumentation]]()
    def update(fd: FunDef, inst: Instrumentation) {
      if (emap.contains(fd))
        emap(fd) :+= inst
      else emap.update(fd, List(inst))
    }
    tprFuncs.map(fd => update(fd, TPR))
    timeFuncs.map(fd => update(fd, Time))
    emap.toMap
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
    case FunctionInvocation(tfd, args) => {
      val remSubInsts = if (tprFuncs.contains(tfd.fd))
        subInsts.slice(0, subInsts.length - 1)
      else subInsts
      if (sccs(fd)(tfd.fd)) {
        remSubInsts.foldLeft(costOfExpr(e) : Expr)(
          (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
      }
      else {
        val allSubInsts = remSubInsts :+ si.selectInst(tfd.fd)(funInvResVar.get, Time)
        allSubInsts.foldLeft(costOfExpr(e) : Expr)(
          (acc: Expr, subeTime: Expr) => Plus(subeTime, acc))
      }
    }
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