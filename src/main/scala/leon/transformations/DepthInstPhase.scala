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

object DepthCostModel {
  val typedMaxFun = TypedFunDef(InstUtil.maxFun, Seq())

  def costOf(e: Expr): Int =
    e match {
      case FunctionInvocation(fd, args) => 1
      case t: Terminal => 0
      case _ => 1
    }

  def costOfExpr(e: Expr) = InfiniteIntegerLiteral(costOf(e))
}

class DepthInstrumenter(p: Program, si: SerialInstrumenter) extends Instrumenter(p, si) {
  import DepthCostModel._

  def inst = Depth

  def functionsToInstrument(): Map[FunDef, List[Instrumentation]] = {
    //find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
    val instFunSet = getRootFuncs().foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))
    instFunSet.map(x => (x, List(Depth))).toMap
  }

  def additionalfunctionsToAdd(): Seq[FunDef] = Seq()// - max functions are inlined, so they need not be added

  def instrumentMatchCase(me: MatchExpr, mc: MatchCase,
    caseExprCost: Expr, scrutineeCost: Expr): Expr = {
    val costMatch = costOfExpr(me)
    def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = 0
    combineDepthIds(costMatch, List(caseExprCost, scrutineeCost))
  }

  def instrument(e: Expr, subInsts: Seq[Expr], funInvResVar: Option[Variable] = None)(implicit fd: FunDef, letIdMap: Map[Identifier, Identifier]): Expr = {
    val costOfParent = costOfExpr(e)
    e match {
      case Variable(id) if letIdMap.contains(id) =>
        // add the cost of instrumentation here
        Plus(costOfParent, si.selectInst(fd)(letIdMap(id).toVariable, inst))

      case t: Terminal => costOfParent
      case FunctionInvocation(tfd, args) =>
        val depthvar = subInsts.last
        val remSubInsts = subInsts.slice(0, subInsts.length - 1)
        val costofOp = {
          costOfParent match {
            case InfiniteIntegerLiteral(x) if (x == 0) => depthvar
            case _ => Plus(costOfParent, depthvar)
          }
        }
        combineDepthIds(costofOp, remSubInsts)
      case e : Let =>
        //in this case, ignore the depth of the value, it will included if the bounded variable is
        // used in the body
        combineDepthIds(costOfParent, subInsts.tail)
      case _ =>
        val costofOp = costOfParent
        combineDepthIds(costofOp, subInsts)
    }
  }

  def instrumentIfThenElseExpr(e: IfExpr, condInst: Option[Expr],
    thenInst: Option[Expr], elzeInst: Option[Expr]): (Expr, Expr) = {

    val cinst = condInst.toList
    val tinst = thenInst.toList
    val einst = elzeInst.toList

    (combineDepthIds(zero, cinst ++ tinst), combineDepthIds(zero, cinst ++ einst))
  }

  def combineDepthIds(costofOp: Expr, subeInsts: Seq[Expr]): Expr = {
    if (subeInsts.size == 0) costofOp
    else if (subeInsts.size == 1) Plus(costofOp, subeInsts(0))
    else {
      //optimization: remove duplicates from 'subeInsts' as 'max' is an idempotent operation
      val head +: tail = subeInsts.distinct
      val summand = tail.foldLeft(head: Expr)((acc, id) => {
        (acc, id) match {
          case (InfiniteIntegerLiteral(x), _) if (x == 0) => id
          case (_, InfiniteIntegerLiteral(x)) if (x == 0) => acc
          case _ =>
            FunctionInvocation(typedMaxFun, Seq(acc, id))
        }
      })
      costofOp match {
        case InfiniteIntegerLiteral(x) if (x == 0) => summand
        case _ => Plus(costofOp, summand)
      }
    }
  }
}
