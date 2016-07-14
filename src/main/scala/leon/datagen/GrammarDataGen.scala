/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package datagen

import purescala.Expressions._
import purescala.Types._
import purescala.Common._
import purescala.Constructors._
import purescala.Extractors._
import purescala.ExprOps._
import evaluators._
import bonsai.enumerators._

import grammars._
import utils.UniqueCounter
import utils.SeqUtils.cartesianProduct

/** Utility functions to generate values of a given type.
  * In fact, it could be used to generate *terms* of a given type,
  * e.g. by passing trees representing variables for the "bounds". */
class GrammarDataGen(evaluator: Evaluator, grammar: ExpressionGrammar = ValueGrammar) extends DataGenerator {
  implicit val ctx = evaluator.context

  // Assume e contains generic values with index 0.
  // Return a series of expressions with all normalized combinations of generic values.
  private def expandGenerics(e: Expr): Seq[Expr] = {
    val c = new UniqueCounter[TypeParameter]
    val withUniqueCounters: Expr = postMap {
      case GenericValue(t, _) =>
        Some(GenericValue(t, c.next(t)))
      case _ => None
    }(e)

    val indices = c.current

    val (tps, substInt) = (for {
      tp <- indices.keySet.toSeq
    } yield tp -> (for {
      from <- 0 to indices(tp)
      to <- 0 to from
    } yield (from, to))).unzip

    val combos = cartesianProduct(substInt)

    val substitutions = combos map { subst =>
      tps.zip(subst).map { case (tp, (from, to)) =>
        (GenericValue(tp, from): Expr) -> (GenericValue(tp, to): Expr)
      }.toMap
    }

    substitutions map (replace(_, withUniqueCounters))

  }

  def generate(tpe: TypeTree): Iterator[Expr] = {
    val enum = new MemoizedEnumerator[Label, Expr, ProductionRule[Label, Expr]](grammar.getProductions)
    enum.iterator(Label(tpe)).flatMap(expandGenerics).takeWhile(_ => !interrupted.get)
  }

  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]] = {

    def filterCond(vs: Seq[Expr]): Boolean = satisfying match {
      case BooleanLiteral(true) =>
        true
      case e =>
        // in -> e should be enough. We shouldn't find any subexpressions of in.
        evaluator.eval(e, (ins zip vs).toMap) match {
          case EvaluationResults.Successful(BooleanLiteral(true)) => true
          case _ => false
        }
    }

    if (ins.isEmpty) {
      Iterator(Seq[Expr]()).filter(filterCond)
    } else {
      val values = generate(tupleTypeWrap(ins.map{ _.getType }))

      val detupled = values.map {
        v => unwrapTuple(v, ins.size)
      }

      detupled.take(maxEnumerated)
              .filter(filterCond)
              .take(maxValid)
              .takeWhile(_ => !interrupted.get)
    }
  }

  def generateMapping(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int) = {
    generateFor(ins, satisfying, maxValid, maxEnumerated) map (ins zip _)
  }

}
