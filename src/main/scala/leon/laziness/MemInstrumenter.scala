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
        TPR -> new MemTPRInstrumenter(p, si))

  val serialInst = new SerialInstrumenter(p, instrumenterFactory, Some(exprInstFactory))

  def apply: Program = serialInst.apply

  class MemExprInstrumenter(ictx: InstruContext) extends ExprInstrumenter(ictx: InstruContext) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1)

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
              IfExpr(ElementOfSet(cc, stExpr),
                InfiniteIntegerLiteral(costOfMemoization(m.inst)),
                selectInst(instId.toVariable, m.inst))
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

  /**
   * Here, we assume that all match cases of dispatch function take the same cost.
   */
  class MemTimeInstrumenter(p: Program, si: SerialInstrumenter) extends TimeInstrumenter(p, si) {
    import timeCostModel._
    override def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
      val costMatch = costOfExpr(me)
      val costOfPattern = patternCost(mc.pattern, false, true)
      val cumulativeCostOfPattern =
        if(isEvalFunction(fd))
           costOfPattern // ignoring the cost of previous cases
        else
          me.cases.take(me.cases.indexOf(mc)).foldLeft(0)((acc, currCase) => acc + patternCost(currCase.pattern, false, false)) + costOfPattern
      Plus(costMatch, Plus(Plus(InfiniteIntegerLiteral(cumulativeCostOfPattern), caseExprCost), scrutineeCost))
    }
  }

  /**
   * Here, we assume that all match cases of dispatch function take the same cost.
   */
  class MemTPRInstrumenter(p: Program, si: SerialInstrumenter) extends TPRInstrumenter(p, si) {
    import timeCostModel._
    override def instrumentMatchCase(me: MatchExpr, mc: MatchCase, caseExprCost: Expr, scrutineeCost: Expr)(implicit fd: FunDef): Expr = {
      val costMatch = costOfExpr(me)
      val costOfPattern = patternCost(mc.pattern, false, true)
      val cumulativeCostOfPattern =
        if(isEvalFunction(fd))
           costOfPattern // ignoring the cost of previous cases
        else
          me.cases.take(me.cases.indexOf(mc)).foldLeft(0)((acc, currCase) => acc + patternCost(currCase.pattern, false, false)) + costOfPattern
      Plus(costMatch, Plus(Plus(InfiniteIntegerLiteral(cumulativeCostOfPattern), caseExprCost), scrutineeCost))
    }
  }
}
