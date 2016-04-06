/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Common._

import scala.collection.mutable.{HashMap => MutableMap}

/** Represents a context-free grammar of expressions */
abstract class ExpressionGrammar {

  private[this] val cache = new MutableMap[Label, Seq[ProductionRule[Label, Expr]]]()

  /** The list of production rules for this grammar for a given nonterminal.
    *
    * @param lab The nonterminal for which production rules will be generated
    * @note This is the cached version of [[computeProductions]]. Clients should use this method.
    */
  final def getProductions(lab: Label)(implicit ctx: LeonContext) = {
    cache.getOrElse(lab, {
      val res = applyAspects(lab, computeProductions(lab))
      cache += lab -> res
      res
    })
  }

  /** The list of production rules for this grammar for a given nonterminal.
    *
    * @param lab The nonterminal for which production rules will be generated
    * @note Clients should use the cached version, [[getProductions]] instead
    */
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]]

  protected def applyAspects(lab: Label, ps: Seq[ProductionRule[Label, Expr]])(implicit ctx: LeonContext) = {
    lab.aspects.foldLeft(ps) {
      case (ps, a) => a.applyTo(lab, ps)
    }
  }

  /** Union of grammars */
  final def ||(that: ExpressionGrammar): ExpressionGrammar = {
    Union(Seq(this, that))
  }

  final def printProductions(printer: String => Unit)(implicit ctx: LeonContext) {
    def sorter(lp1: (Label, Seq[ProductionRule[Label, Expr]]), lp2: (Label, Seq[ProductionRule[Label, Expr]])): Boolean = {
      val l1 = lp1._1
      val l2 = lp2._1

      val os1 = l1.aspects.collectFirst { case aspects.Sized(size) => size }
      val os2 = l2.aspects.collectFirst { case aspects.Sized(size) => size }

      (os1, os2) match {
        case (Some(s1), Some(s2)) =>
          if (s1 > s2) {
            true
          } else if (s1 == s2) {
            l1.asString < l2.asString
          } else {
            false
          }
        case _ => l1.asString < l2.asString
      }
    }

    for ((lab, gs) <- cache.toSeq.sortWith(sorter)) {
      val lhs = f"${Console.BOLD}${lab.asString}%50s${Console.RESET} ::= "

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
