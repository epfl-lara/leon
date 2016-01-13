/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import purescala.Types.Typed
import utils.SeqUtils._

/** Adds information about size to a nonterminal symbol */
case class SizedNonTerm[T <: Typed](underlying: T, size: Int) extends Typed {
  val getType = underlying.getType

  override def asString(implicit ctx: LeonContext) = underlying.asString+"|"+size+"|"
}

/** Limits a grammar by producing expressions of size bounded by the [[SizedNonTerm.size]] of a given [[SizedNonTerm]].
  *
  * In case of commutative operations, the grammar will produce trees skewed to the right
  * (i.e. the right subtree will always be larger). Notice we do not lose generality in case of
  * commutative operations.
  */
case class SizeBoundedGrammar[T <: Typed](g: ExpressionGrammar[T], optimizeCommut: Boolean) extends ExpressionGrammar[SizedNonTerm[T]] {
  def computeProductions(sl: SizedNonTerm[T])(implicit ctx: LeonContext): Seq[Prod] = {
    if (sl.size <= 0) {
      Nil
    } else if (sl.size == 1) {
      g.getProductions(sl.underlying).filter(_.isTerminal).map { gen =>
        terminal(gen.builder(Seq()), gen.tag)
      }
    } else {
      g.getProductions(sl.underlying).filter(_.isNonTerminal).flatMap { gen =>

        // Ad-hoc equality that does not take into account position of nonterminals.
        // TODO: Ugly and hacky
        def characteristic(t: T): AnyRef = t match {
          case TaggedNonTerm(underlying, tag, _, isConst) =>
            (underlying, tag, isConst)
          case other =>
            other
        }

        // Optimization: When we have a commutative operation and all the labels are the same,
        // we can skew the expression to always be right-heavy
        val sizes = if(optimizeCommut && Tags.isCommut(gen.tag) && gen.subTrees.map(characteristic).toSet.size == 1) {
          sumToOrdered(sl.size-1, gen.arity)
        } else {
          sumTo(sl.size-1, gen.arity)
        }

        for (ss <- sizes) yield {
          val subSizedLabels = (gen.subTrees zip ss) map (s => SizedNonTerm(s._1, s._2))

          nonTerminal(subSizedLabels, gen.builder, gen.tag)
        }
      }
    }
  }
}
