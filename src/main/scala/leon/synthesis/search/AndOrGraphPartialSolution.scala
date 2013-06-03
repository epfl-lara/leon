/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.search

class AndOrGraphPartialSolution[AT <: AOAndTask[S],
                                OT <: AOOrTask[S],
                                S](val g: AndOrGraph[AT, OT, S], missing: AT => S, includeUntrusted: Boolean) {


  def getSolution: S = {
    solveOr(g.tree)
  }

  def solveAnd(t: g.AndTree): S = {
    if (t.isSolved && (includeUntrusted || t.isTrustworthy)) {
      t.solution.get
    } else {
      t match {
      case l: g.AndLeaf =>
        missing(t.task)
      case n: g.AndNode =>
        n.task.composeSolution(n.subProblems.values.map(solveOr(_)).toList).getOrElse(missing(t.task))
      }
    }
  }

  def solveOr(t: g.OrTree): S = {
    if (t.isSolved && (includeUntrusted || t.isTrustworthy)) {
      t.solution.get
    } else {
      t match {
        case l: g.OrLeaf =>
          missing(l.parent.task)
        case n: g.OrNode =>
          solveAnd(n.minAlternative)
      }
    }
  }
}
