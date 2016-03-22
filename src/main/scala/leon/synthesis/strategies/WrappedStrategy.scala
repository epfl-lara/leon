/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import synthesis.graph._

class WrappedStrategy(underlying: Strategy) extends Strategy {

  override def init(root: RootNode) = underlying.init(root)

  override def getNextToExpand(from: Node): Option[Node] = {
    underlying.getNextToExpand(from)
  }

  override def bestAlternative(on: OrNode): Option[Node] = {
    underlying.bestAlternative(on)
  }

  override def beforeExpand(n: Node) = {
    underlying.beforeExpand(n)
  }

  override def afterExpand(n: Node) = {
    underlying.afterExpand(n);
  }

  override def interrupt() = underlying.interrupt()

  override def recoverInterrupt() = underlying.recoverInterrupt()

  def debugInfoFor(n: Node) = underlying.debugInfoFor(n)
}
