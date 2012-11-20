package leon.synthesis.search

abstract class AndOrGraphSearch[AT <: AOAndTask[S],
                                OT <: AOOrTask[S],
                                S <: AOSolution](val g: AndOrGraph[AT, OT, S]) {

  def nextLeaf: Option[g.Leaf] = {
    var c: g.Tree = g.tree
    var res: Option[g.Leaf] = None

    while(res.isEmpty) {
      c match {
        case l: g.Leaf =>
          res = Some(l)

        case an: g.AndNode =>
          c = (an.subProblems -- an.subSolutions.keySet).values.minBy(_.minCost)

        case on: g.OrNode =>
          c = on.minAlternative
      }
    }

    res
  }

  abstract class ExpandResult[T <: AOTask[S]]
  case class Expanded[T <: AOTask[S]](sub: List[T]) extends ExpandResult[T]
  case class ExpandSuccess[T <: AOTask[S]](sol: S) extends ExpandResult[T]
  case class ExpandFailure[T <: AOTask[S]]() extends ExpandResult[T]

  var continue = true

  def search(): Option[S] = {
    while (!g.tree.isSolved && continue && !g.tree.isUnsolvable) {
      nextLeaf match {
        case Some(l) =>
          l match {
            case al: g.AndLeaf =>
              processAndLeaf(al.task) match {
                case Expanded(ls) =>
                  al.expandWith(ls)
                case r @ ExpandSuccess(sol) =>
                  al.solution = Some(sol)
                  al.parent.notifySolution(al, sol)
                case _ =>
                  al.parent.unsolvable(al)
              }
            case ol: g.OrLeaf =>
              processOrLeaf(ol.task) match {
                case Expanded(ls) =>
                  ol.expandWith(ls)
                case r @ ExpandSuccess(sol) =>
                  ol.solution = Some(sol)
                  ol.parent.notifySolution(ol, sol)
                case _ =>
                  ol.parent.unsolvable(ol)
              }
          }
        case None =>
          continue = false
      }
    }
    
    g.tree.solution
  }

  def processAndLeaf(l: AT): ExpandResult[OT]
  def processOrLeaf(l: OT): ExpandResult[AT]
}
