/* Copyright 2009-2016 EPFL, Lausanne */

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

object objCostModel {
  def costOf(e: Expr): Int = e match {
  	case CaseClass(_, _) => 1
    case t: Terminal => 0
    case _ => 0
  }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}

class ObjAllocInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  import objCostModel._

  def inst = Obj

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
    val instFunSet = getRootFuncs().foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd)).filter(_.hasBody) // ignore uninterpreted functions
    //println("Root funs: "+getRootFuncs().map(_.id).mkString(",")+" All funcs: "+ instFunSet.map(_.id).mkString(","))
    instFunSet.map(x => (x, List(Obj))).toMap
  }

  def additionalfunctionsToAdd() = Seq()

  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
    caseExprCost: Expr, scrutineeCost: Expr): Expr = {
    val costMatch = costOfExpr(me)
    def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = 0
    //Plus(costMatch, Plus(caseExprCost, scrutineeCost))
    Plus(costMatch, caseExprCost)
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
  	(implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    case t: Terminal => costOfExpr(t)
    case _ =>
      subInsts.foldLeft(costOfExpr(e) : Expr)(
        (acc: Expr, subeObjAlloc: Expr) => Plus(subeObjAlloc, acc))
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {    
  	val costIf = costOfExpr(e)
    (Plus(costIf, Plus(condInst.get, thenInst.get)),
      Plus(costIf, Plus(condInst.get, elzeInst.get)))
  }
}
