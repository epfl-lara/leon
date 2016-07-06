/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._

import graph._
import strategies._

class PartialSolution(strat: Strategy, includeUntrusted: Boolean = false)(implicit ctx: LeonContext) {

  def includeSolution(s: Solution) = {
    includeUntrusted || s.isTrusted
  }

  def completeProblem(p: Problem) = {
    Solution.choose(p)
  }

  def solutionAround(n: Node): Expr => Option[Solution] = {
    def solveWith(optn: Option[Node], from: Node, sol: Solution): Option[Solution] = optn match {
      case None =>
        Some(sol)

      case Some(on: OrNode) =>
        solveWith(on.parent, on, sol)

      case Some(an: AndNode) =>
        val ssols = for (d <- an.descendants) yield {
          if (d == from) {
            sol
          } else {
            getSolutionFor(d)
          }
        }

        an.ri.onSuccess(ssols).flatMap { nsol =>
          solveWith(an.parent, an, nsol)
        }
    }

    e : Expr => solveWith(n.parent, n, Solution(BooleanLiteral(true), Set(), e))
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
          //println("AN:"+an.toString)
          an.ri.onSuccess(n.descendants.map(getSolutionFor)) match {
            case Some(sol) =>
              //println("Sol!")
              sol

            case None =>
              //println("No Sol!")
              completeProblem(an.ri.problem)
          }
        } else {
          completeProblem(an.ri.problem)
        }
    }
  }
}
