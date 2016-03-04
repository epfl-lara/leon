/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Types._

abstract class SimpleExpressionGrammar extends ExpressionGrammar {

  type Prod = ProductionRule[TypeTree, Expr]

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[TypeTree, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[TypeTree], builder: (Seq[Expr] => Expr), tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[TypeTree, Expr](subs, builder, tag, cost)
  }

  def filter(f: Prod => Boolean) = {
    new SimpleExpressionGrammar {
      def computeProductions(lab: TypeTree)(implicit ctx: LeonContext) = {
        SimpleExpressionGrammar.this.computeProductions(lab).filter(f)
      }
    }
  }

  /** The list of production rules for this grammar for a given nonterminal
    *
    * @param lab The nonterminal for which production rules will be generated
    */
  def computeProductions(lab: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] = {
    computeProductions(lab.getType).map { p =>
      ProductionRule(p.subTrees.map(Label(_)), p.builder, p.tag, p.cost)
    }
  }

  def computeProductions(tpe: TypeTree)(implicit ctx: LeonContext): Seq[ProductionRule[TypeTree, Expr]]
}
