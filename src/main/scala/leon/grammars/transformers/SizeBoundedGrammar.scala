/* Copyright 2009-2016 EPFL, Lausanne */

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
    } else {
      val (terminals, nonTerminals) = g.getProductions(sl.underlying).partition(_.isTerminal)

      val termProds = terminals.filter(_.cost == sl.size).map { gen =>
        terminal(gen.builder(Seq()), gen.tag, gen.cost)
      }

      val recProds = nonTerminals.filter(_.cost < sl.size).flatMap { gen =>
        // Ad-hoc equality that does not take into account position etc.of TaggedNonTerminal's
        // TODO: Ugly and hacky
        def characteristic(t: T): Typed = t match {
          case TaggedNonTerm(underlying, _, _, _) =>
            underlying
          case other =>
            other
        }

        // Optimization: When we have a commutative operation and all the labels are the same,
        // we can skew the expression to always be right-heavy
        val sizes = if(optimizeCommut && Tags.isCommut(gen.tag) && gen.subTrees.map(characteristic).toSet.size == 1) {
          sumToOrdered(sl.size-gen.cost, gen.arity)
        } else {
          sumTo(sl.size-gen.cost, gen.arity)
        }

        for (ss <- sizes) yield {
          val subSizedLabels = (gen.subTrees zip ss) map (s => SizedNonTerm(s._1, s._2))

          gen.copy(subTrees = subSizedLabels)
        }
      }

      termProds ++ recProds
    }
  }
}
