/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import leon.purescala.Extractors.{IsTyped, TopLevelAnds}
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Types._
import solvers.{PartialModel, Model}

abstract class ContextualEvaluator(ctx: LeonContext, prog: Program, val maxSteps: Int) extends Evaluator(ctx, prog) with CEvalHelpers {

  protected implicit val _ = ctx

  type RC <: RecContext[RC]
  type GC <: GlobalContext

  def initRC(mappings: Map[Identifier, Expr]): RC
  def initGC(model: solvers.Model, check: Boolean): GC

  case class EvalError(msg : String) extends Exception {
    override def getMessage = msg + Option(super.getMessage).map("\n" + _).getOrElse("")
  }
  case class RuntimeError(msg : String) extends Exception
  case class QuantificationError(msg: String) extends Exception

  // Used by leon-web, please do not delete
  var lastGC: Option[GC] = None

  def eval(ex: Expr, model: Model) = {
    try {
      lastGC = Some(initGC(model, check = true))
      ctx.timers.evaluators.recursive.runtime.start()
      EvaluationResults.Successful(e(ex)(initRC(model.toMap), lastGC.get))
    } catch {
      case EvalError(msg) =>
        EvaluationResults.EvaluatorError(msg)
      case so: StackOverflowError =>
        EvaluationResults.RuntimeError("Stack overflow")
      case e @ RuntimeError(msg) =>
        EvaluationResults.RuntimeError(msg)
      case jre: java.lang.RuntimeException =>
        EvaluationResults.RuntimeError(jre.getMessage)
    } finally {
      ctx.timers.evaluators.recursive.runtime.stop()
    }
  }

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): Value

  def typeErrorMsg(tree : Expr, expected : TypeTree) : String = s"Type error : expected ${expected.asString}, found ${tree.asString} of type ${tree.getType}."

}

private[evaluators] trait CEvalHelpers {
  this: ContextualEvaluator =>

  /* This is an effort to generalize forall to non-det. solvers
    def forallInstantiations(gctx:GC, fargs: Seq[ValDef], conj: Expr) = {

      val henkinModel: PartialModel = gctx.model match {
        case hm: PartialModel => hm
        case _ => throw EvalError("Can't evaluate foralls without henkin model")
      }

      val vars = variablesOf(conj)
      val args = fargs.map(_.id).filter(vars)
      val quantified = args.toSet

      val matcherQuorums = extractQuorums(conj, quantified)

      matcherQuorums.flatMap { quorum =>
        var mappings: Seq[(Identifier, Int, Int)] = Seq.empty
        var constraints: Seq[(Expr, Int, Int)] = Seq.empty

        for (((expr, args), qidx) <- quorum.zipWithIndex) {
          val (qmappings, qconstraints) = args.zipWithIndex.partition {
            case (Variable(id), aidx) => quantified(id)
            case _ => false
          }

          mappings ++= qmappings.map(p => (p._1.asInstanceOf[Variable].id, qidx, p._2))
          constraints ++= qconstraints.map(p => (p._1, qidx, p._2))
        }

        var equalities: Seq[((Int, Int), (Int, Int))] = Seq.empty
        val mapping = for ((id, es) <- mappings.groupBy(_._1)) yield {
          val base :: others = es.toList.map(p => (p._2, p._3))
          equalities ++= others.map(p => base -> p)
          (id -> base)
        }

        val argSets = quorum.foldLeft[List[Seq[Seq[Expr]]]](List(Seq.empty)) {
          case (acc, (expr, _)) => acc.flatMap(s => henkinModel.domain(expr).map(d => s :+ d))
        }

        argSets.map { args =>
          val argMap: Map[(Int, Int), Expr] = args.zipWithIndex.flatMap {
            case (a, qidx) => a.zipWithIndex.map { case (e, aidx) => (qidx, aidx) -> e }
          }.toMap

          val map = mapping.map { case (id, key) => id -> argMap(key) }
          val enabler = andJoin(constraints.map {
            case (e, qidx, aidx) => Equals(e, argMap(qidx -> aidx))
          } ++ equalities.map {
            case (k1, k2) => Equals(argMap(k1), argMap(k2))
          })

          (enabler, map)
        }
      }*/



}
