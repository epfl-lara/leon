/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import synthesis.graph._

case class BoundedStrategy(underlying: Strategy, bound: Int) extends WrappedStrategy(underlying) {
  private[this] var nSteps = 0

  override def getNextToExpand(from: Node): Option[Node] = {
    if (nSteps < bound) {
      super.getNextToExpand(from)
    } else {
      None
    }
  }

  override def afterExpand(n: Node) = {
    super.afterExpand(n);
    nSteps += 1
  }
}
