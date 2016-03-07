/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package strategies

import synthesis.graph._

class CostBasedStrategy(ctx: LeonContext, cm: CostModel) extends Strategy {
  private var bestSols = Map[Node, Option[Solution]]()
  private var bestCosts = Map[Node, Cost]()

  override def init(root: RootNode): Unit = {
    super.init(root)
    computeBestSolutionFor(root)
  }

  def computeBestSolutionFor(n: Node): Option[Solution] = {
    val res = if (n.isSolved) {
      Some(n.generateSolutions().head)
    } else if (n.isDeadEnd) {
      None
    } else if (!n.isExpanded) {
      n match {
        case an: AndNode =>
          an.ri.onSuccess match {
            case SolutionBuilderCloser(_) =>
              Some(Solution.simplest(an.p.outType))

            case SolutionBuilderDecomp(types, recomp) =>
              recomp(types.toList.map(Solution.simplest))
          }
        case on: OrNode =>
          Some(Solution.simplest(n.p.outType))
      }
    } else {
      n match {
        case an: AndNode =>
          val subs = an.descendants.map(bestSolutionFor)

          if (subs.forall(_.isDefined)) {
            an.ri.onSuccess(subs.flatten)
          } else {
            None
          }
        case on: OrNode =>
          on.descendants.foreach(bestSolutionFor)

          bestSolutionFor(on.descendants.minBy(bestCosts))
      }
    }

    bestSols += n -> res
    bestCosts += n -> res.map(cm.solution _).getOrElse(cm.impossible)

    res
  }

  def bestAlternative(on: OrNode): Option[Node] = {
    if (on.isDeadEnd) {
      None
    } else {
      Some(on.descendants.minBy(bestCosts))
    }
  }

  def bestSolutionFor(n: Node): Option[Solution] = {
    bestSols.get(n) match {
      case Some(os) => os
      case None => computeBestSolutionFor(n)
    }
  }

  def recomputeCost(n: Node): Unit = {
    val oldCost = bestCosts(n)
    computeBestSolutionFor(n)

    if (bestCosts(n) != oldCost) {
      n.parent.foreach(recomputeCost)
    }
  }

  override def afterExpand(n: Node): Unit = {
    super.afterExpand(n)

    for (d <- n.descendants) {
      bestSolutionFor(d)
    }

    recomputeCost(n)
  }

  def debugInfoFor(n: Node) = bestCosts.get(n).map(_.toString).getOrElse("?")
}
