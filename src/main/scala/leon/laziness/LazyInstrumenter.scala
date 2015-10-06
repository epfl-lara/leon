package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import leon.verification.AnalysisPhase
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.transformations._
import LazinessUtil._

class LazyInstrumenter(p: Program) {

  def apply: Program = {
    val exprInstFactory = (x: Map[FunDef, FunDef], y: SerialInstrumenter, z: FunDef) =>
      new LazyExprInstrumenter(x, y)(z)
    (new SerialInstrumenter(p, Some(exprInstFactory))).apply
  }

  class LazyExprInstrumenter(funMap: Map[FunDef, FunDef], serialInst: SerialInstrumenter)(implicit currFun: FunDef)
      extends ExprInstrumenter(funMap, serialInst)(currFun) {

    val costOfMemoization: Map[Instrumentation, Int] =
      Map(Time -> 1, Stack -> 1, Rec -> 1, TPR -> 1, Depth -> 1)

    override def apply(e: Expr): Expr = {
      if (isEvalFunction(currFun)) {
        val closureParam = currFun.params(0).id.toVariable
        val stateParam = currFun.params(1).id.toVariable
        val nbody = super.apply(e)
        val bodyId = FreshIdentifier("bd", nbody.getType, true)
        val instExprs = instrumenters map { m =>
          IfExpr(ElementOfSet(closureParam, stateParam),
              //SubsetOf(FiniteSet(Set(closureParam), closureParam.getType), stateParam),
            InfiniteIntegerLiteral(costOfMemoization(m.inst)),
            selectInst(bodyId.toVariable, m.inst))
        }
        Let(bodyId, nbody,
          Tuple(TupleSelect(bodyId.toVariable, 1) +: instExprs))

      } else super.apply(e)
    }
  }
}
