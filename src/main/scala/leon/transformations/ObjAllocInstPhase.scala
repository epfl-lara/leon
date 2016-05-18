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
  	// TODO
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

  def instrumentMatchCase(
    // TODO
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
  	(implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    // TODO
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {
    // TODO
  }

}
