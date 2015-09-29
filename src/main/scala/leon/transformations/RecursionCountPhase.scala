package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.utils._
import invariant.util.Util._

class RecursionCountInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {

  def inst = Rec

  val sccs = cg.graph.sccs.flatMap { scc =>
    scc.map(fd => (fd -> scc.toSet))
  }.toMap

  /**
   * Instrument only those functions that are in the same sccs of the root functions
   */
  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    val instFunSet = getRootFuncs().flatMap(sccs.apply _)
    instFunSet.map(x => (x, List(Rec))).toMap
  }

  override def additionalfunctionsToAdd(): Seq[FunDef] = Seq.empty[FunDef]

  def addSubInstsIfNonZero(subInsts: Seq[Expr], init: Expr): Expr = {
    subInsts.foldLeft(init) {
      case (acc, subinst) if subinst != zero =>
        if (acc == zero) subinst
        else Plus(acc, subinst)
    }
  }

  def instrumentMatchCase(me: MatchExpr,
    mc: MatchCase,
    caseExprCost: Expr,
    scrutineeCost: Expr): Expr = {
    Plus(caseExprCost, scrutineeCost)
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
    (implicit fd: FunDef, leIdtMap: Map[Identifier,Identifier]): Expr = e match {
    case FunctionInvocation(TypedFunDef(callee, _), _) if sccs(fd)(callee) =>
      //this is a recursive call
      //Note that the last element of subInsts is the instExpr of the invoked function
      addSubInstsIfNonZero(subInsts, one)
    case FunctionInvocation(TypedFunDef(callee, _), _) if si.funcInsts.contains(callee) && si.funcInsts(callee).contains(this.inst) =>
      //this is not a recursive call, so do not consider the cost of the callee
      //Note that the last element of subInsts is the instExpr of the invoked function
      addSubInstsIfNonZero(subInsts.take(subInsts.size - 1), zero)
    case _ =>
      //add the cost of every sub-expression
      addSubInstsIfNonZero(subInsts, zero)
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr], thenInst: Option[Expr],
    elzeInst: Option[Expr]): (Expr, Expr) = {

    val cinst = condInst.toList
    val tinst = thenInst.toList
    val einst = elzeInst.toList

    (addSubInstsIfNonZero(cinst ++ tinst, zero),
      addSubInstsIfNonZero(cinst ++ einst, zero))
  }
}