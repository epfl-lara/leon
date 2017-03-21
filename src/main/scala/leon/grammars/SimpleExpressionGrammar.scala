/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import purescala.Types._
import purescala.TypeOps.instantiateType
import purescala.Definitions._

case class SGenericProd(
  tparams: Seq[TypeParameterDef],
  label: TypeTree,
  args: Seq[TypeTree],
  builder: Map[TypeParameter, TypeTree] => ProductionRule[TypeTree, Expr]
)

/** An [[ExpressionGrammar]] whose productions for a given [[Label]]
  * depend only on the underlying [[TypeTree]] of the label
  */
abstract class SimpleExpressionGrammar extends ExpressionGrammar {

  type SProd = ProductionRule[TypeTree, Expr]

  def tpeToLabel(tpe: TypeTree): Label = Label(tpe)

  def convertProd(p: SProd): Prod = {
    ProductionRule[Label, Expr](p.subTrees.map(tpeToLabel), p.builder, p.tag, p.cost, p.logProb)
  }

  final def generateProductions(implicit ctx: LeonContext) = {
    generateSimpleProductions.map { gp =>
      GenericProdSeed(gp.tparams, tpeToLabel(gp.label), gp.args, { tmap => convertProd(gp.builder(tmap)) })
    }
  }

  def generateSimpleProductions(implicit ctx: LeonContext): Seq[SGenericProd]


  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def sTerminal(
      label: TypeTree,
      builder: => Expr,
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      logProb: Double = -1.0) = {

    SGenericProd(Nil, label, Nil, tmap => ProductionRule[TypeTree, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost, logProb))
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def sNonTerminal(
      label: TypeTree,
      subs: Seq[TypeTree],
      builder: (Seq[Expr] => Expr),
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      logProb: Double = -1.0) = {

    SGenericProd(Nil, label, Nil, tmap => ProductionRule[TypeTree, Expr](subs, builder, tag, cost, logProb))
  }

  def sGeneric(
      tps: Seq[TypeParameterDef],
      label: TypeTree,
      subs: Seq[TypeTree],
      builder: (Seq[Expr] => Expr),
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      weight: Double = -1.0) = {

    val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>
      ProductionRule[TypeTree, Expr](subs.map(instantiateType(_, tmap)), es => instantiateType(builder(es), tmap, Map()), tag, cost, weight)
    }

    SGenericProd(tps, label, subs, prodBuilder)
  }

}
