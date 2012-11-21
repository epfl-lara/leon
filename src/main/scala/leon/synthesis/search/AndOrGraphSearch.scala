package leon.synthesis.search

abstract class AndOrGraphSearch[AT <: AOAndTask[S],
                                OT <: AOOrTask[S],
                                S <: AOSolution](val g: AndOrGraph[AT, OT, S]) {

  def nextLeaf: Option[g.Leaf] = {
    import collection.mutable.PriorityQueue

    case class WT(t: g.Tree, prefixCost: Cost) extends Ordered[WT] {
      val cost = t.minCost + prefixCost

      def compare(that: WT) = that.cost.compare(this.cost) // DESC
    }

    val q = new PriorityQueue[WT]()
    q += WT(g.tree, Cost.zero)

    var res: Option[g.Leaf] = None

    while(res.isEmpty && !q.isEmpty) {
      q.dequeue() match {
        case WT(l: g.Leaf, c) =>
          res = Some(l)

        case WT(an: g.AndNode, c) =>
          if (!an.isSolved) {
            q ++= (an.subProblems -- an.subSolutions.keySet).values.map(n => WT(n, c + an.minCost))
          }

        case WT(on: g.OrNode, c) =>
          if (!on.isSolved) {
            q ++= on.alternatives.values.map(n => WT(n, c + on.minCost))
          }

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
    while (!g.tree.isSolved && continue) {
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
                  al.isUnsolvable = true
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
                  ol.isUnsolvable = true
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
