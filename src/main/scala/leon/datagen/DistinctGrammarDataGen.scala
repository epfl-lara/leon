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
import utils.StreamUtils.cartesianProduct

/** Utility functions to generate values of a given type.
  * In fact, it could be used to generate *terms* of a given type,
  * e.g. by passing trees representing variables for the "bounds". */
class VaryingGrammarDataGen(eval: Evaluator, grammar: ExpressionGrammar = ValueGrammar) extends GrammarDataGen(eval, grammar) {

  def generateN(tpe: TypeTree, n: Int): Iterator[Seq[Expr]] = {
    if (n == 1) {
      generate(tpe).map(Seq(_))
    } else {
      generate(tpe).sliding(n).filter(_.size == n)
    }
  }

  override def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]] = {
    require(satisfying == BooleanLiteral(true))

    if (ins.isEmpty) {
      Iterator(Seq[Expr]())
    } else {
      // From id1: A, id2: B, id3: A
      // We get: (id1, id3), (id2)
      val groups = ins.groupBy(_.getType).values.toSeq

      // id1 -> 0, id2 -> 2, id3 -> 1
      val indices = groups.flatten.zipWithIndex.toMap

      // Generate distinct values for each group
      var streams = groups map { g =>
        generateN(g.head.getType, g.size).toStream
      }

      // Group1 x Group2 ...
      val values = cartesianProduct(streams).map(_.flatten).map { vs =>
        // obtain Seq(v1, v2, v3) where v1 is value of id1 ...
        ins.map(in => vs(indices(in)))
      }.toIterator

      values.take(maxValid).takeWhile(_ => !interrupted.get)
    }
  }
}
