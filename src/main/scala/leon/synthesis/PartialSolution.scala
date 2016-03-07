/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._

import graph._
import strategies._

class PartialSolution(strat: Strategy, includeUntrusted: Boolean = false) {

  def includeSolution(s: Solution) = {
    includeUntrusted || s.isTrusted
  }

  def completeProblem(p: Problem) = {
    Solution.choose(p)
  }

  def solutionAround(n: Node): Expr => Option[Solution] = {
    def solveWith(optn: Option[Node], sol: Solution): Option[Solution] = optn match {
      case None =>
        Some(sol)

      case Some(n) => n.parent match {
        case None =>
          Some(sol)

        case Some(on: OrNode) =>
          solveWith(on.parent, sol)

        case Some(an: AndNode) =>
          val ssols = for (d <- an.descendants) yield {
            if (d == n) {
              sol
            } else {
              getSolutionFor(d)
            }
          }

          an.ri.onSuccess(ssols).flatMap { nsol =>
            solveWith(an.parent, nsol)
          }
      }
    }

    e : Expr => solveWith(Some(n), Solution(BooleanLiteral(true), Set(), e))

  }

  def getSolutionFor(n: Node): Solution = {
    n match {
      case on: OrNode =>
        if (on.isSolved) {
          val sols = on.generateSolutions()
          sols.find(includeSolution) match {
            case Some(sol) =>
              return sol
            case _ =>
          }
        }

        if (n.isExpanded) {
          strat.bestAlternative(on) match {
            case None => completeProblem(on.p)
            case Some(d) => getSolutionFor(d)
          }
        } else {
          completeProblem(on.p)
        }
      case an: AndNode =>
        if (an.isSolved) {
          val sols = an.generateSolutions()
          sols.find(includeSolution) match {
            case Some(sol) =>
              return sol
            case _ =>
          }
        }

        if (n.isExpanded) {
          an.ri.onSuccess(n.descendants.map(getSolutionFor)) match {
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
