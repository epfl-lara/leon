/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import bonsai._

import purescala.Expressions._
import purescala.Types._
import purescala.Common._

import scala.collection.mutable.{HashMap => MutableMap}

abstract class ExpressionGrammar[T <: Typed] {
  type Gen = Generator[T, Expr]

  private[this] val cache = new MutableMap[T, Seq[Gen]]()

  def terminal(builder: => Expr) = {
    Generator[T, Expr](Nil, { (subs: Seq[Expr]) => builder })
  }

  def nonTerminal(subs: Seq[T], builder: (Seq[Expr] => Expr)): Generator[T, Expr] = {
    Generator[T, Expr](subs, builder)
  }

  def getProductions(t: T)(implicit ctx: LeonContext): Seq[Gen] = {
    cache.getOrElse(t, {
      val res = computeProductions(t)
      cache += t -> res
      res
    })
  }

  def computeProductions(t: T)(implicit ctx: LeonContext): Seq[Gen]

  def filter(f: Gen => Boolean) = {
    new ExpressionGrammar[T] {
      def computeProductions(t: T)(implicit ctx: LeonContext) = ExpressionGrammar.this.computeProductions(t).filter(f)
    }
  }

  final def ||(that: ExpressionGrammar[T]): ExpressionGrammar[T] = {
    Union(Seq(this, that))
  }


  final def printProductions(printer: String => Unit)(implicit ctx: LeonContext) {
    for ((t, gs) <- cache; g <- gs) {
      val subs = g.subTrees.map { t =>
        FreshIdentifier(Console.BOLD+t.asString+Console.RESET, t.getType).toVariable
      }

      val gen = g.builder(subs).asString

      printer(f"${Console.BOLD}${t.asString}%30s${Console.RESET} ::= $gen")
    }
  }
}
