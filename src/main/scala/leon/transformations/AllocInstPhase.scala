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
import invariant.util._
import Util._
import ProgramUtil._
import TypeUtil._

class AllocInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  def costOf(e: Expr)(implicit currFun: FunDef): Int = e match {
    case CaseClass(_, _) => 1
    case t: Terminal => 0
    case _ => 0
  }

  def costOfExpr(e: Expr)(implicit currFun: FunDef) = InfiniteIntegerLiteral(costOf(e))

  def inst = Alloc

  val (funsToInst, funTypesToInst) = {
    val funToFTypes = userLevelFunctions(p).map { fd =>
      def rec(e: Expr): Set[CompatibleType] = e match {
        case NoTree(_) => Set()
        case l@Lambda(_, b) => rec(b) + new CompatibleType(l.getType)
        case Ensuring(b, Lambda(_, p)) => rec(b) ++ rec(p)
        case Operator(args, op) => args.toSet flatMap rec
      }
      fd -> rec(fd.fullBody)
    }.toMap

    def functionCreatingTypes(fts: Set[CompatibleType]) =
      funToFTypes.collect {
        case (fd, ftypes) if !ftypes.intersect(fts).isEmpty => fd
      }
    var (instFuns, instFunTypes) = getRootFuncs()
    var newFuns = instFuns ++ functionCreatingTypes(instFunTypes)
    while(!newFuns.isEmpty) {
      //println("newfuns: "+newFuns.map(_.id))
      // (a) find all function types of applications in the nextSets
      val appTypes = newFuns flatMap {
        case ifd if ifd.hasBody =>
          collect[CompatibleType] {
            case Application(l, _) => Set(new CompatibleType(l.getType))
            case _ => Set()
          }(ifd.body.get)
        case _ => Set[CompatibleType]()
      }
      // (b) find all userLevelFunctions that may create a lambda compatible with the types of the application.
      val newRoots = functionCreatingTypes(appTypes)
      // (c) find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
      val nextFunSet = (newFuns ++ newRoots).flatMap(cg.transitiveCallees).toSet
      //println("nextFunSet: "+nextFunSet.map(_.id))
      newFuns = nextFunSet -- instFuns
      instFuns ++= nextFunSet
      instFunTypes ++= appTypes
    }
    (instFuns, instFunTypes)
  }

  override def missCost() = {
    InfiniteIntegerLiteral(1)
  } 

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    //println("Root funs: "+getRootFuncs().map(_.id).mkString(",")+" All funcs: "+ instFunSet.map(_.id).mkString(","))
    funsToInst.map(x => (x, List(Alloc))).toMap
  }

  def functionTypesToInstrument(): Map[CompatibleType, List[Instrumentation]] = {
    funTypesToInst.map(x => (x, List(Alloc))).toMap
  }

  def additionalfunctionsToAdd() = Seq()

  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
    caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
    val costMatch = costOfExpr(me)
    def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = 0
    Plus(costMatch, Plus(caseExprCost, scrutineeCost))
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)
  	(implicit fd: FunDef, letIdMap: Map[Identifier,Identifier]): Expr = e match {
    case t: Terminal => costOfExpr(t)
    case _ =>
      subInsts.foldLeft(costOfExpr(e) : Expr)(
        (acc: Expr, subeObjAlloc: Expr) => Plus(subeObjAlloc, acc))
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
      thenInst: Option[Expr], elzeInst: Option[Expr])(implicit currFun: FunDef): (Expr, Expr) = {    
  	val costIf = costOfExpr(e)
    (Plus(costIf, Plus(condInst.get, thenInst.get)),
      Plus(costIf, Plus(condInst.get, elzeInst.get)))
  }
}
