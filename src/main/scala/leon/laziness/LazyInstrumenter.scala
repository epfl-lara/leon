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

class LazyInstrumenter(p: Program, ctx: LeonContext, clFactory: ClosureFactory) {

  val exprInstFactory = (x: Map[FunDef, FunDef], y: SerialInstrumenter, z: FunDef) =>
      new LazyExprInstrumenter(x, y)(z)
  val serialInst = new SerialInstrumenter(p, Some(exprInstFactory))

  def apply: Program = serialInst.apply

  class LazyExprInstrumenter(funMap: Map[FunDef, FunDef], serialInst: SerialInstrumenter)(implicit currFun: FunDef)
      extends ExprInstrumenter(funMap, serialInst)(currFun) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1)

    override def apply(e: Expr): Expr = {
      if (isEvalFunction(currFun)) {
        val stateParam = currFun.params.last.id.toVariable // Currently, all evals take a state
        e match {
          case MatchExpr(scr, mcases) =>
            val ncases = mcases map {
              case mc@MatchCase(pat@InstanceOfPattern(Some(bind), CaseClassType(ccd: CaseClassDef, tps)), guard, body) =>
                // find the case class of a memoized function that is constructed
                val memoCCs = collect[CaseClass]{
                  case cc@CaseClass(CaseClassType(ccd, _),_) if clFactory.memoClosures(ccd) => Set(cc)
                  case _ => Set()
                }(body)
                val instBody = transform(body)(Map())
                val nbody = if(memoCCs.isEmpty){ // this case is not invoking a memoized function
                  instBody
                } else {
                  if(memoCCs.size > 1)
                    throw new IllegalStateException("More than one case class construction found in match case! "+mc)
                  val memoClosure = memoCCs.head
                  val bodyId = FreshIdentifier("bd", instBody.getType, true)
                  val instExprs = instrumenters map { m =>
                    IfExpr(ElementOfSet(memoClosure, stateParam),
                      InfiniteIntegerLiteral(costOfMemoization(m.inst)),
                      selectInst(bodyId.toVariable, m.inst))
                  }
                  Let(bodyId, instBody,
                    Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))
                }
                MatchCase(pat, guard, nbody)
            }
            MatchExpr(scr, ncases)
        }
      } else
        super.apply(e)
    }
  }
}
