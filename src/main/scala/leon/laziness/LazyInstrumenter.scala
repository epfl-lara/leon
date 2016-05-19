package leon
package laziness

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.transformations._
import LazinessUtil._

class LazyInstrumenter(p: Program, ctx: LeonContext, clFactory: ClosureFactory, funManager: FunctionsManager) {

  val exprInstFactory = (x: Map[FunDef, FunDef], y: SerialInstrumenter, z: FunDef) =>
      new MemExprInstrumenter(x, y)(z)
  val serialInst = new SerialInstrumenter(p, Some(exprInstFactory))

  def apply: Program = serialInst.apply

  class MemExprInstrumenter(funMap: Map[FunDef, FunDef], serialInst: SerialInstrumenter)(implicit currFun: FunDef)
      extends ExprInstrumenter(funMap, serialInst)(currFun) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1)

    lazy val stateParam = currFun.params.last.id.toVariable // this field should be valid when it is accessed

    def memoClosureByName(name: String) = {
      clFactory.memoClasses.find{
        case (fd, ccdef) => name == fd.id.name
      }.get
    }

    def stateTps(st: Expr) = st.getType.asInstanceOf[SetType].base.asInstanceOf[ClassType].tps

    override def tupleifyCall(f: FunctionInvocation, subeVals: List[Expr], subeInsts: Map[Instrumentation, List[Expr]])(implicit letIdMap: Map[Identifier, Identifier]): Expr = {
      val target = f.tfd.fd
      val instExpr = super.tupleifyCall(f, subeVals, subeInsts)
      if(isMemoized(target)) {
        val (oldTarget, ccdef) = memoClosureByName(InstUtil.userFunctionName(target))
        val (args, stExpr) =
          if(funManager.funsNeedStates(oldTarget)) {
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
    }
  }
}
