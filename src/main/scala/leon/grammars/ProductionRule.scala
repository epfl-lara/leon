/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import scala.language.existentials
import bonsai.Generator

/** Represents a production rule of a non-terminal symbol of an [[ExpressionGrammar]].
 *
 * @param subTrees The nonterminals that are used in the right-hand side of this [[ProductionRule]]
 *                 (and will generate deeper syntax trees).
 * @param builder A function that builds the syntax tree that this [[ProductionRule]] represents from nested trees.
 * @param tag Gives information about the nature of this production rule.
 * @param cost The cost of applying this rule
 * @param weight The absolute (unnormalized) weight of this rule (based on a corpus)
 * @tparam T The type of nonterminal symbols of the grammar
 * @tparam R The type of syntax trees of the grammar
 */
case class ProductionRule[T, R](
    override val subTrees: Seq[T],
    override val builder: Seq[R] => R,
    outType: Class[_ <: R],
    tag: Tags.Tag,
    cost: Int,
    weight: Double)
extends Generator[T,R](subTrees, builder)
