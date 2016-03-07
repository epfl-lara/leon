/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import synthesis.graph._

class TimeSlicingStrategy(ctx: LeonContext) extends Strategy {

  var timeSpent = Map[Node, Long]().withDefaultValue(0l)

  def bestAlternative(on: OrNode): Option[Node] = {
    on.descendants.filter(_.isOpen).sortBy(timeSpent).headOption
  }

  def recordTime(from: Node, t: Long): Unit = {
    timeSpent += from -> (timeSpent(from) + t)

    from.parent.foreach {
      recordTime(_, t)
    }
  }

  var tstart: Long = 0;

  override def beforeExpand(n: Node): Unit = {
    super.beforeExpand(n)
    tstart = System.currentTimeMillis
  }

  override def afterExpand(n: Node): Unit = {
    super.afterExpand(n)

    val t = System.currentTimeMillis - tstart
    recordTime(n, t)
  }

  def debugInfoFor(n: Node) = timeSpent.get(n).map(_.toString).getOrElse("?")
}
