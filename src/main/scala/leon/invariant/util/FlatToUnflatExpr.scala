package leon
package invariant.util

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import solvers._
import scala.collection.immutable._
import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}
import ExpressionTransformer._
import leon.evaluators._
import EvaluationResults._

/**
 *A class that can used to compress a flattened expression
 * and also expand the compressed models to the flat forms
 */
class FlatToUnflatExpr(ine: Expr, eval: DeterministicEvaluator) {

  val (unflate, flatIdMap) = unFlattenWithMap(ine)
  def getModel(m: Model) = new FlatModel(m)

  /**
   * Expands the model into a model with mappings for identifiers.
   * Note: this class cannot be accessed in parallel.
   */
  class FlatModel(initModel: Model) {
    var idModel = initModel.toMap

    def apply(iden: Identifier) = {
      var seen = Set[Identifier]()
      def recBind(id: Identifier): Expr = {
        val idv = idModel.get(id)
        if (idv.isDefined) idv.get
        else {
          if (seen(id)) {
            //we are in a cycle here
            throw new IllegalStateException(s"$id depends on itself $id, input expression: $ine")
          } else if (flatIdMap.contains(id)) {
            val rhs = flatIdMap(id)
            // recursively bind all freevars to values (we can ignore the return values)
            seen += id
            variablesOf(rhs).map(recBind)
            eval.eval(rhs, idModel) match {
              case Successful(v) =>
                idModel += (id -> v)
                v
              case _ =>
                throw new IllegalStateException(s"Evaluation Falied for $rhs")
            }
          } else
            throw new IllegalStateException(s"Cannot extract model $id as it is not a part of the input expression: $ine")
        }
      }
      recBind(iden)
    }
  }
}