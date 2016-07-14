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
    def noExtraCost(os: Option[Solution]) = {
      os.map(s => (s, Cost(0)))
    }

    val res: Option[(Solution, Cost)] = if (n.isSolved) {
      noExtraCost(n.generateSolutions().headOption)
    } else if (n.isDeadEnd) {
      None
    } else if (!n.isExpanded) {
      n match {
        case an: AndNode =>
          an.ri.onSuccess match {
            case SolutionBuilderCloser(_, cost) =>
              Some((Solution.simplest(an.p.outType), cost))

            case SolutionBuilderDecomp(types, recomp) =>
              noExtraCost(recomp(types.toList.map(Solution.simplest)))
          }
        case on: OrNode =>
          noExtraCost(Some(Solution.simplest(n.p.outType)))
      }
    } else {
      noExtraCost(n match {
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
      })
    }

    val osol = res.map(_._1)

    bestSols += n -> osol
    bestCosts += n -> res.map {
      case (sol, extraCost) => cm.solution(sol) + extraCost
    }.getOrElse(cm.impossible)

    osol
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
