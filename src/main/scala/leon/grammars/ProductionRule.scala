/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import bonsai.Generator

/** Represents a production rule of a non-terminal symbol of an [[ExpressionGrammar]].
 *
 *  @param subTrees The nonterminals that are used in the right-hand side of this [[ProductionRule]]
 *                  (and will generate deeper syntax trees).
 *  @param builder A function that builds the syntax tree that this [[ProductionRule]] represents from nested trees.
 *  @param tag Gives information about the nature of this production rule.
 *  @tparam T The type of nonterminal symbols of the grammar
 *  @tparam R The type of syntax trees of the grammar
 */
case class ProductionRule[T, R](override val subTrees: Seq[T], override val builder: Seq[R] => R, tag: Tags.Tag, cost: Int)
  extends Generator[T,R](subTrees, builder)
