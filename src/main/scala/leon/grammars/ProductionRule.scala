/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

/** Represents a production rule of a non-terminal symbol of an [[ExpressionGrammar]].
 *
 * @param subTrees The nonterminals that are used in the right-hand side of this [[ProductionRule]]
 *                 (and will generate deeper syntax trees).
 * @param builder A function that builds the syntax tree that this [[ProductionRule]] represents from nested trees.
 * @param tag Gives information about the nature of this production rule.
 * @param cost The cost of applying this rule (positive integer).
 * @param logProb Logarithmic probability of this rule being instantiated for a given nonterminal (based on a corpus)
  *               (will be a negative number).
 * @tparam T The type of nonterminal symbols of the grammar
 * @tparam R The type of syntax trees of the grammar
 */
case class ProductionRule[T, R](
    subTrees: Seq[T],
    builder: Seq[R] => R,
    tag: Tags.Tag,
    cost: Int,
    logProb: Double)
{
  require(logProb <= 0.0 && cost > 0)

  val arity = subTrees.size

  val isTerminal    = arity == 0
  val isNonTerminal = arity > 0
}
