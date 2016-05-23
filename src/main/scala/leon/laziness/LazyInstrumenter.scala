package leon
package laziness

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.transformations._
import LazinessUtil._

class LazyInstrumenter(p: Program, ctx: LeonContext, clFactory: LazyClosureFactory) {

  val exprInstFactory = (x: Map[FunDef, FunDef], y: SerialInstrumenter, z: FunDef) =>
      new LazyExprInstrumenter(x, y)(z)
  val serialInst = new SerialInstrumenter(p, Some(exprInstFactory))
  /*def funsWithInstSpecs  = {
    serialInst.instToInstrumenter.values.flatMap{inst =>
      inst.getRootFuncs(p)
    }.toList.distinct
  }*/

  def apply: Program = serialInst.apply

  class LazyExprInstrumenter(funMap: Map[FunDef, FunDef], serialInst: SerialInstrumenter)(implicit currFun: FunDef)
      extends ExprInstrumenter(funMap, serialInst)(currFun) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1)

    override def apply(e: Expr): Expr = {
      if (isEvalFunction(currFun)) {
        val closureParam = currFun.params(0).id.toVariable
        val stateParam = currFun.params(1).id.toVariable
        // we need to specialize instrumentation of body
        val nbody = e match {
          case MatchExpr(scr, mcases) =>
            val ncases = mcases map {
              case MatchCase(pat, guard, body) =>
                // instrument the state part (and ignore the val part)
                // (Note: this is an hack to ensure that we always consider only one call to targets)
                /*val transState = transform(statepart)(Map())
                val transVal = transform(valpart)(Map())

                val caseId = FreshIdentifier("cd", transState.getType, true)
                val casePart = Tuple(Seq(TupleSelect(transVal, 1), TupleSelect(caseId.toVariable, 1)))
                val instPart = instrumenters map { m => selectInst(caseId.toVariable, m.inst) }
                val lete = Let(caseId, transState, Tuple(casePart +: instPart))*/
                MatchCase(pat, guard, transform(body)(Map()))
            }
            MatchExpr(scr, ncases)
        }
        //val nbody = super.apply(e)
        val bodyId = FreshIdentifier("bd", nbody.getType, true)
        // we need to select the appropriate field of the state
        val lazyTname = adtNameToTypeName(typeNameWOParams(closureParam.getType))
        val setField = clFactory.selectFieldOfState(lazyTname, stateParam,
            stateParam.getType.asInstanceOf[CaseClassType])
        val instExprs = instrumenters map { m =>
          IfExpr(ElementOfSet(closureParam, setField),
            InfiniteIntegerLiteral(costOfMemoization(m.inst)),
            selectInst(bodyId.toVariable, m.inst))
        }
        Let(bodyId, nbody,
          Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))
      } else
        super.apply(e)
    }
  }
}
