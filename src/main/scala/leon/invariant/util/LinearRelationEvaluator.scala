package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import evaluators._
import java.io._
import solvers._
import solvers.combinators._
import solvers.smtlib._
import solvers.z3._
import scala.util.control.Breaks._
import purescala.ScalaPrinter
import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.runtime.universe
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.util.ExpressionTransformer._
import invariant.structure._
import invariant.structure.FunctionUtils._

import Util._
import PredicateUtil._
import SolverUtil._
import RealValuedExprEvaluator._

/**
   * Evaluator for a predicate that is a simple equality/inequality between two variables.
   * Some expressions cannot be evaluated, so we return none in those cases.
   */
class LinearRelationEvaluator(ctx: InferenceContext) {
  
  def predEval(model: LazyModel): (Expr => Option[Boolean]) = {
    if (ctx.usereals) realEval(model)
    else intEval(model)
  }

  def intEval(model: LazyModel): (Expr => Option[Boolean]) = {
    def modelVal(id: Identifier): BigInt = {
      val InfiniteIntegerLiteral(v) = model(id)
      v
    }
    def eval: (Expr => Option[Boolean]) = {
      case And(args) =>
        val argres = args.map(eval)
        if (argres.exists(!_.isDefined)) None
        else
          Some(argres.forall(_.get))
      case Equals(Variable(id1), Variable(id2)) =>
        if (model.isDefinedAt(id1) && model.isDefinedAt(id2))
          Some(model(id1) == model(id2)) //note: ADTs can also be compared for equality
        else None
      case LessEquals(Variable(id1), Variable(id2)) => Some(modelVal(id1) <= modelVal(id2))
      case GreaterEquals(Variable(id1), Variable(id2)) => Some(modelVal(id1) >= modelVal(id2))
      case GreaterThan(Variable(id1), Variable(id2)) => Some(modelVal(id1) > modelVal(id2))
      case LessThan(Variable(id1), Variable(id2)) => Some(modelVal(id1) < modelVal(id2))
      case e => throw new IllegalStateException("Predicate not handled: " + e)
    }
    eval
  }

  def realEval(model: LazyModel): (Expr => Option[Boolean]) = {
    def modelVal(id: Identifier): FractionalLiteral = {
      //println("Identifier: "+id)
      model(id).asInstanceOf[FractionalLiteral]
    }
    {
      case Equals(Variable(id1), Variable(id2)) => Some(model(id1) == model(id2)) //note: ADTs can also be compared for equality
      case e @ Operator(Seq(Variable(id1), Variable(id2)), op) if (e.isInstanceOf[LessThan]
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals]) => {
        Some(evaluateRealPredicate(op(Seq(modelVal(id1), modelVal(id2)))))
      }
      case e => throw new IllegalStateException("Predicate not handled: " + e)
    }
  }
}
