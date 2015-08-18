/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.TypeOps._

import leon.utils.SeqUtils.sumTo

case class SizedLabel[T <% Typed](underlying: T, size: Int) extends Typed {
  val getType = underlying.getType

  override def asString(implicit ctx: LeonContext) = underlying.asString+"|"+size+"|"
}

case class SizeBoundedGrammar[T <% Typed](g: ExpressionGrammar[T]) extends ExpressionGrammar[SizedLabel[T]] {
  def computeProductions(sl: SizedLabel[T])(implicit ctx: LeonContext): Seq[Gen] = {
    if (sl.size <= 0) {
      Nil
    } else if (sl.size == 1) {
      g.getProductions(sl.underlying).filter(_.subTrees.isEmpty).map { gen =>
        terminal(gen.builder(Seq()))
      }
    } else {
      g.getProductions(sl.underlying).filter(_.subTrees.nonEmpty).flatMap { gen =>
        val sizes = sumTo(sl.size-1, gen.subTrees.size)

        for (ss <- sizes) yield {
          val subSizedLabels = (gen.subTrees zip ss) map (s => SizedLabel(s._1, s._2))

          nonTerminal(subSizedLabels, gen.builder)
        }
      }
    }
  }
}
