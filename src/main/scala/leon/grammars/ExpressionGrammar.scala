/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Types._
import purescala.Common._
import transformers.Union

import scala.collection.mutable.{HashMap => MutableMap}

/** Represents a context-free grammar of expressions
  *
  * @tparam T The type of nonterminal symbols for this grammar
  */
abstract class ExpressionGrammar[T <: Typed] {

  type Prod = ProductionRule[T, Expr]

  private[this] val cache = new MutableMap[T, Seq[Prod]]()

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[T, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[T], builder: (Seq[Expr] => Expr), tag: Tags.Tag = Tags.Top, cost: Int = 1): ProductionRule[T, Expr] = {
    ProductionRule[T, Expr](subs, builder, tag, cost)
  }

  /** The list of production rules for this grammar for a given nonterminal.
    * This is the cached version of [[getProductions]] which clients should use.
    *
    * @param t The nonterminal for which production rules will be generated
    */
  def getProductions(t: T)(implicit ctx: LeonContext): Seq[Prod] = {
    cache.getOrElse(t, {
      val res = computeProductions(t)
      cache += t -> res
      res
    })
  }

  /** The list of production rules for this grammar for a given nonterminal
    *
    * @param t The nonterminal for which production rules will be generated
    */
  def computeProductions(t: T)(implicit ctx: LeonContext): Seq[Prod]

  def filter(f: Prod => Boolean) = {
    new ExpressionGrammar[T] {
      def computeProductions(t: T)(implicit ctx: LeonContext) = ExpressionGrammar.this.computeProductions(t).filter(f)
    }
  }

  final def ||(that: ExpressionGrammar[T]): ExpressionGrammar[T] = {
    Union(Seq(this, that))
  }


  final def printProductions(printer: String => Unit)(implicit ctx: LeonContext) {
    for ((t, gs) <- cache.toSeq.sortBy(_._1.asString)) {
      val lhs = f"${Console.BOLD}${t.asString}%50s${Console.RESET} ::= "
      if (gs.isEmpty) {
        printer(s"${lhs}ε")
      } else {
        val rhs = for (g <- gs) yield {
          val subs = g.subTrees.map { t =>
            FreshIdentifier(Console.BOLD + t.asString + Console.RESET, t.getType).toVariable
          }

          g.builder(subs).asString
        }
        printer(lhs + rhs.mkString("\n" + " " * 55))
      }
    }
  }
}
