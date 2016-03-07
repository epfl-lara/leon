/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import synthesis.graph._

import leon.utils.Interruptible

abstract class Strategy extends Interruptible {

  // Nodes to consider next
  private var openNodes = Set[Node]()

  def init(root: RootNode): Unit = {
    openNodes += root
  }

  /**
   * Standard-next for AndNodes, strategy-best for OrNodes
   */
  def bestNext(n: Node): Option[Node] = {
    n match {
      case an: AndNode =>
        an.descendants.find(_.isOpen)

      case on: OrNode =>
        bestAlternative(on)
    }
  }

  def bestAlternative(on: OrNode): Option[Node]

  def getNextToExpand(root: Node): Option[Node] = {
    if (openNodes(root)) {
      Some(root)
    } else if (openNodes.isEmpty) {
      None
    } else {
      bestNext(root).flatMap(getNextToExpand)
    }
  }

  def beforeExpand(n: Node): Unit = {}

  def afterExpand(n: Node): Unit = {
    openNodes -= n
    openNodes ++= n.descendants
  }

  def interrupt() = {}

  def recoverInterrupt() = {}

  def debugInfoFor(n: Node): String
}


