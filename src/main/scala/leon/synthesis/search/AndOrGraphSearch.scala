package leon.synthesis.search

abstract class AndOrGraphSearch[AT <: AOAndTask[S],
                                OT <: AOOrTask[S],
                                S <: AOSolution](val g: AndOrGraph[AT, OT, S]) {

  def nextLeaves(k: Int): List[g.Leaf] = {
    import scala.math.Ordering.Implicits._

    case class WL(t: g.Leaf, costs: List[Int])

    var leaves = List[WL]()

    def collectFromAnd(at: g.AndTree, costs: List[Int]) {
      val newCosts = at.task.cost.value :: costs
      at match {
        case l: g.Leaf =>
          collectLeaf(WL(l, newCosts.reverse)) 
        case a: g.AndNode =>
          for (o <- (a.subProblems -- a.subSolutions.keySet).values) {
            collectFromOr(o, newCosts)
          }
      }
    }

    def collectFromOr(ot: g.OrTree, costs: List[Int]) {
      val newCosts = ot.task.cost.value :: costs

      ot match {
        case l: g.Leaf =>
          collectLeaf(WL(l, newCosts.reverse)) 
        case o: g.OrNode =>
          for (a <- o.alternatives.values) {
            collectFromAnd(a, newCosts)
          }
      }
    }

    def collectLeaf(wl: WL) {
      leaves = wl :: leaves
    }

    collectFromOr(g.tree, Nil)

    leaves.sortBy(_.costs).map(_.t)
  }

  def nextLeafNotSimple: Option[g.Leaf] = nextLeaves(1).headOption

  def nextLeafSimple: Option[g.Leaf] = {
    var c : g.Tree = g.tree

    var res: Option[g.Leaf] = None

    while(res.isEmpty) {
      c match {
        case l: g.Leaf =>
          res = Some(l)

        case an: g.AndNode =>
          c = (an.subProblems -- an.subSolutions.keySet).values.minBy(_.minCost)

        case on: g.OrNode =>
          c = on.alternatives.values.minBy(_.minCost)
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
      nextLeaves(1) match {
        case l :: _ =>
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
        case Nil =>
          continue = false
      }
    }
    g.tree.solution
  }

  def processAndLeaf(l: AT): ExpandResult[OT]
  def processOrLeaf(l: OT): ExpandResult[AT]
}
