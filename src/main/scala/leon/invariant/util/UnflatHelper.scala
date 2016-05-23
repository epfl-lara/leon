package leon
package invariant.util

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import solvers._
import scala.collection.immutable._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }
import ExpressionTransformer._
import leon.evaluators._
import EvaluationResults._

trait LazyModel {
  def get(iden: Identifier): Option[Expr]

  def apply(iden: Identifier): Expr =
    get(iden) match {
      case Some(e) => e
      case _       => throw new IllegalStateException(s"Cannot create mapping for $iden")
    }

  def isDefinedAt(iden: Identifier) = get(iden).isDefined
}

class SimpleLazyModel(m: Model) extends LazyModel {
  def get(iden: Identifier): Option[Expr] = m.get(iden)
}

/**
 * Expands a given model into a model with mappings for identifiers introduced during flattening.
 * Note: this class cannot be accessed in parallel.
 */
class FlatModel(freeVars: Set[Identifier], flatIdMap: Map[Identifier, Expr], initModel: Model, eval: DefaultEvaluator) extends LazyModel {
  var idModel = initModel.toMap

  override def get(iden: Identifier) = {
    var seen = Set[Identifier]()
    def recBind(id: Identifier): Option[Expr] = {
      val idv = idModel.get(id)
      if (idv.isDefined) idv
      else {
        if (seen(id)) {
          //we are in a cycle here
          throw new IllegalStateException(s"$id depends on itself")
        } else if (flatIdMap.contains(id)) {
          val rhs = flatIdMap(id)
          // recursively bind all freevars to values (we can ignore the return values)
          seen += id
          variablesOf(rhs).filterNot(idModel.contains).map(recBind)
          eval.eval(rhs, idModel) match {
            case Successful(v) =>
              idModel += (id -> v)
              Some(v)
            case _ =>
              None
              //throw new IllegalStateException(s"Evaluation Falied for $id -> $rhs")
          }
        } else if (freeVars(id)) {
          // here, `id` either belongs to values of the flatIdMap, or to flate or was lost in unflattening
          println(s"Completing $id with simplest value")
          val simpv = simplestValue(id.getType)
          idModel += (id -> simpv)
          Some(simpv)
        } else
          None
        //throw new IllegalStateException(s"Cannot extract model $id as it not contained in the input expression: $ine")
      }
    }
    recBind(iden)
  }
}

object UnflatHelper {
  def evaluate(e: Expr, m: LazyModel, eval: DefaultEvaluator): Expr = {
    val varsMap = variablesOf(e).collect {
      case v if m.isDefinedAt(v) => (v -> m(v))
    }.toMap
    eval.eval(e, varsMap) match {
      case Successful(v) => v
      case _ =>
        throw new IllegalStateException(s"Evaluation Falied for $e")
    }
  }
}

/**
 * A class that can used to compress a flattened expression
 * and also expand the compressed models to the flat forms
 */
class UnflatHelper(ine: Expr, excludeIds: Set[Identifier], eval: DefaultEvaluator) {

  val (unflate, flatIdMap) = unflattenWithMap(ine, excludeIds, includeFuns = false)
  val invars = variablesOf(ine)

  def getModel(m: Model) = new FlatModel(invars, flatIdMap, m,  eval)
}