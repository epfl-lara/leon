/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import graph._

class PartialSolution(g: Graph, includeUntrusted: Boolean) {

  def includeSolution(s: Solution) = {
    includeUntrusted || s.isTrusted
  }

  def completeProblem(p: Problem) = {
    Solution.choose(p)
  }


  def getSolution(): Solution = {
    getSolutionFor(g.root)
  }

  def getSolutionFor(n: g.Node): Solution = {
    n match {
      case on: g.OrNode =>
        if (on.isSolved) {
          val sols = on.generateSolutions()
          sols.find(includeSolution) match {
            case Some(sol) =>
              return sol
            case _ =>
          }
        }

        if (n.isExpanded) {
          val descs = on.descendents.filter(_.isClosed)
          if (descs.isEmpty) {
            completeProblem(on.p)
          } else {
            getSolutionFor(descs.minBy(_.histogram))
          }
        } else {
          completeProblem(on.p)
        }
      case an: g.AndNode =>
        if (an.isSolved) {
          val sols = an.generateSolutions()
          sols.find(includeSolution) match {
            case Some(sol) =>
              return sol
            case _ =>
          }
        }

        if (n.isExpanded) {
          an.ri.onSuccess(n.descendents.map(getSolutionFor)) match {
            case Some(sol) =>
              sol

            case None =>
              completeProblem(an.ri.problem)
          }
        } else {
          completeProblem(an.ri.problem)
        }
    }
  }
}
