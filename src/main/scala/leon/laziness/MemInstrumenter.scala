package leon
package laziness

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.transformations._
import HOMemUtil._

class MemInstrumenter(p: Program, ctx: LeonContext, clFactory: ClosureFactory, funManager: FunctionsManager) {

  val exprInstFactory = (ictx: InstruContext) => new MemExprInstrumenter(ictx)

  val instrumenterFactory: SerialInstrumenter => Map[Instrumentation, Instrumenter] =
    si => Map(Time -> new MemTimeInstrumenter(p, si),
      Depth -> new DepthInstrumenter(p, si),
      Rec -> new RecursionCountInstrumenter(p, si),
      Stack -> new StackSpaceInstrumenter(p, si),
      TPR -> new MemTPRInstrumenter(p, si),
      Alloc -> new MemAllocInstrumenter(p, si))

  val serialInst = new SerialInstrumenter(p, instrumenterFactory, Some(exprInstFactory))

  def apply: Program = {
    serialInst.apply
  }

  class MemExprInstrumenter(ictx: InstruContext) extends ExprInstrumenter(ictx: InstruContext) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1, Alloc -> 0)

    lazy val stateParam = ictx.currFun.params.last.id.toVariable // this field should be valid when it is accessed

    def memoClosureByName(name: String) = {
      clFactory.memoClasses.find {
        case (fd, ccdef) => name == fd.id.name
      }.get
    }

    def stateTps(st: Expr) = st.getType.asInstanceOf[SetType].base.asInstanceOf[ClassType].tps

    override def tupleifyCall(f: Expr, subeVals: List[Expr], subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
      import ictx._
      f match {
        case FunctionInvocation(TypedFunDef(target, _), _) =>
          //      /val target = f.tfd.fd
          val instExpr = super.tupleifyCall(f, subeVals, subeInsts)
          if (isMemoized(target)) {
            val (oldTarget, ccdef) = memoClosureByName(InstUtil.userFunctionName(target))
            val (args, stExpr) =
              if (funManager.funsNeedStates(oldTarget)) {
                //remove the state argument
                (subeVals.dropRight(1), subeVals.last)
              } else {
                throw new IllegalStateException("Cannot access the state at this point!!")
                //(subeVals, stateParam)
              }
            val cc = CaseClass(CaseClassType(ccdef, stateTps(stExpr)), args)
            val instId = FreshIdentifier("instd", instExpr.getType, true)
            val instExprs = instrumenters map { m =>
              val hitCost = InfiniteIntegerLiteral(costOfMemoization(m.inst))
              val missCost = m.missCost()
              IfExpr(ElementOfSet(cc, stExpr), hitCost,
                Plus(missCost, selectInst(instId.toVariable, m.inst)))
            }
            Let(instId, instExpr,
              Tuple(TupleSelect(instId.toVariable, 1) +: instExprs))
          } else {
            instExpr
          }
        case _: Application =>
          throw new IllegalStateException("Seen application in Lazy Instrumenter!!")
      }
    }
  }

  object memTimeCostModel {
    def costOf(e: Expr)(implicit currFun: FunDef): Int = {
      val cost = e match {
        case _ if isEvalFunction(currFun)               => 0 // cost of every operation inside eval is zero (note the cost of targets of `eval` will be included anyway)
        case FunctionInvocation(fd, _) if !fd.hasBody   => 0 // uninterpreted functions
        case FunctionInvocation(fd, args)               => 1
        case t: Terminal                                => 0
        case _: Let                                     => 0
        case Tuple(Seq(_, s)) if isStateType(s.getType) => 0 // state construction
        case TupleSelect(se, _) => se.getType match {
          case TupleType(Seq(_, stType)) if isStateType(stType) => 0 // state extraction
          case _ => 1
        }
        case FiniteSet(_, clType) if isMemoClosure(clType) => 0 // creating a memo set
        case CaseClass(cct, _) if isMemoClosure(cct.root) => 0 // creating a memo closure
        case SetUnion(s1, _) if isStateType(s1.getType) => 0 // state union
        case _ => 1
      }
      /*if(currFun.id.name.contains("kthMin")) {
        if(cost != 0)
          println(s"Cost of expression: $e is $cost")
      }*/
      cost
    }
  }

  /**
   * Here, we assume that all match cases of dispatch function take the same cost.
   */
  import leon.invariant.util._
  class MemTimeInstrumenter(p: Program, si: SerialInstrumenter) extends TimeInstrumenter(p, si) {
    override def costOf(e: Expr)(implicit currFd: FunDef): Int = memTimeCostModel.costOf(e)

    override def instProp(e: Expr)(fd: FunDef) =
      if (isEvalFunction(fd)) {
        Some(GreaterEquals(e, Util.zero))
      } else None

    override def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
      if (isEvalFunction(fd)) {
        // ignoring the cost of match completely
        caseExprCost
      } else {
        val costMatch = costOfExpr(me)
        val costOfPattern = patternCost(mc.pattern, false, true)
        val cumulativeCostOfPattern =
          me.cases.take(me.cases.indexOf(mc)).foldLeft(0)((acc, currCase) => acc + patternCost(currCase.pattern, false, false)) + costOfPattern
        Plus(costMatch, Plus(Plus(InfiniteIntegerLiteral(cumulativeCostOfPattern), caseExprCost), scrutineeCost))
      }
    }
  }

  object memAllocCostModel {
    def costOf(e: Expr)(implicit currFun: FunDef): Int = {
      val cost = e match {
        case CaseClass(cct, _) if isMemoClosure(cct.root) => 0
        case CaseClass(_, _) => 1
        case _ => 0
      }
      cost
    }
  }

  class MemAllocInstrumenter(p: Program, si: SerialInstrumenter) extends AllocInstrumenter(p, si) {
    override def costOf(e: Expr)(implicit currFd: FunDef): Int = memAllocCostModel.costOf(e)

    override def instProp(e: Expr)(fd: FunDef) =
      if (isEvalFunction(fd)) {
        Some(GreaterEquals(e, Util.zero))
      } else None

    override def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
      if (isEvalFunction(fd)) {
        // ignoring the cost of match completely
        caseExprCost
      } else {
        val costMatch = costOfExpr(me)
        def totalCostOfMatchPatterns(me: MatchExpr, mc: MatchCase): BigInt = 0
        Plus(costMatch, Plus(caseExprCost, scrutineeCost))
      }
    }
  }

  /**
   * Here, we assume that all match cases of dispatch function take the same cost.
   */
  class MemTPRInstrumenter(p: Program, si: SerialInstrumenter) extends TPRInstrumenter(p, si) {
    override def costOf(e: Expr)(implicit currFd: FunDef): Int = memTimeCostModel.costOf(e)
    override def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
      if (isEvalFunction(fd)) {
        // ignoring the cost of match completely
        caseExprCost
      } else {
        val costMatch = costOfExpr(me)
        val costOfPattern = patternCost(mc.pattern, false, true)
        val cumulativeCostOfPattern =
          me.cases.take(me.cases.indexOf(mc)).foldLeft(0)((acc, currCase) => acc + patternCost(currCase.pattern, false, false)) + costOfPattern
        Plus(costMatch, Plus(Plus(InfiniteIntegerLiteral(cumulativeCostOfPattern), caseExprCost), scrutineeCost))
      }
    }
  }
}
