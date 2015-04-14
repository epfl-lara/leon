/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import graph._

/**
 * This is context passed down rules, and include search-wise context, as well
 * as current search location information
 */
case class SearchContext (
  sctx: SynthesisContext,
  ci: ChooseInfo,
  currentNode: Node,
  search: Search
) {
  val context  = sctx.context
  val reporter = sctx.reporter
  val program  = sctx.program

  def searchDepth = {
    def depthOf(n: Node): Int = n.parent match {
      case Some(n2) => 1+depthOf(n2)
      case None     => 0
    }

    depthOf(currentNode)
  }

  def parentNode: Option[Node] = currentNode.parent
}
