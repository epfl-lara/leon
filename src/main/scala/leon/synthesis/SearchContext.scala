/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import graph._
import purescala.Expressions.Expr

/**
 * This is context passed down rules, and include search-wise context, as well
 * as current search location information
 */
class SearchContext (
  sctx: SynthesisContext,
  val source: Expr,
  val currentNode: Node,
  val search: Search
) extends SynthesisContext(
  sctx,
  sctx.settings,
  sctx.functionContext,
  sctx.program
) {

  def searchDepth = {
    def depthOf(n: Node): Int = n.parent match {
      case Some(n2) => 1+depthOf(n2)
      case None     => 0
    }

    depthOf(currentNode)
  }

  def parentNode: Option[Node] = currentNode.parent

}
