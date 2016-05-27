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
    def solveWith(optn: Option[Node], sol: Solution): Option[Solution] = optn match {
      case None =>
        Some(sol)

      case Some(n) => n.parent match {
        case None =>
          Some(sol)

        case Some(on: OrNode) =>
          solveWith(on.parent, sol)

        case Some(an: AndNode) =>
          println("Solving AN:"+an.asString)

          val ssols = for (d <- an.descendants) yield {
            if (d == n) {
              sol
            } else {
              println("Solving Desc: "+d.asString)
              getSolutionFor(d)
            }
          }

          println("Calling onSuccess for "+an.ri.asString)
          println(" - ssols:"+ssols.map(_.asString))
          println(" result=>:"+an.ri.onSuccess(ssols))

          an.ri.onSuccess(ssols).flatMap { nsol =>
            println("Solution for sub is: "+nsol.asString)
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
