package leon.aographs

trait AOCost extends Ordered[AOCost] {
  def +(that: AOCost): AOCost = AOCostFixed(value + that.value)

  def value: Int

  def compare(that: AOCost) = this.value - that.value
}

case class AOCostFixed(value: Int) extends AOCost

object AOCost {
  val zero = new AOCostFixed(0)
}

trait AOTask[S <: AOSolution] {
  def cost: AOCost
}

trait AOAndTask[S <: AOSolution] extends AOTask[S] {
  def composeSolution(sols: List[S]): S
}

trait AOOrTask[S <: AOSolution] extends AOTask[S] {
}

trait AOSolution {
  def cost: AOCost
}

class AndOrGraph[AT <: AOAndTask[S], OT <: AOOrTask[S], S <: AOSolution](val root: OT) {
  type C = AOCost

  var tree: Tree = RootNode

  trait Tree {
    val task : AOTask[S]
    val parent: Node[_]

    def minCost: C

    def isSolved: Boolean
  }

  abstract class AndTree extends Tree {
    override val task: AT
  }

  abstract class OrTree extends Tree {
    override val task: OT
  }


  trait Leaf extends Tree {
    val minCost: C = task.cost

    def isSolved: Boolean = false
  }

  trait Node[T <: Tree] extends Tree {
    def unsolvable(l: T)
    def notifySolution(sub: T, sol: S)

    var solution: Option[S] = None

    def isSolved: Boolean = solution.isDefined
  }

  case class AndNode(parent: OrNode, subTasks: List[OT], task: AT) extends AndTree with Node[OrTree] {
    var subProblems         = Map[OT, OrTree]()
    var subSolutions        = Map[OT, S]()

    def computeCost = {
      solution match {
        case Some(s) =>
          s.cost
        case _ =>
          val subCosts = subProblems.map { case (t, ot) => subSolutions.get(t).map(_.cost).getOrElse(ot.minCost) }

          subCosts.foldLeft(task.cost)(_ + _)
      }
    }

    var minCost = computeCost

    def unsolvable(l: OrTree) {
      parent.unsolvable(this)
    }

    def expandLeaf(l: OrLeaf, succ: List[AT]) {
      val n = OrNode(this, Map(), l.task)
      n.alternatives = succ.map(t => t -> AndLeaf(n, t)).toMap
      n.minAlternative = n.computeMin

      subProblems += l.task -> n
    }

    def notifySolution(sub: OrTree, sol: S) {
      subSolutions += sub.task -> sol

      if (subSolutions.size == subProblems.size) {
        solution = Some(task.composeSolution(subTasks.map(subSolutions)))
        minCost = computeCost

        notifyParent(solution.get)
      } else {
        minCost = computeCost
      }

    }

    def notifyParent(s: S) {
      parent.notifySolution(this, s)
    }
  }

  object RootNode extends OrLeaf(null, root) {

  }

  case class AndLeaf(parent: OrNode, task: AT) extends AndTree with Leaf {
    def expandWith(succ: List[OT]) {
      parent.expandLeaf(this, succ)
    }

  }


  case class OrNode(parent: AndNode, var alternatives: Map[AT, AndTree], task: OT) extends OrTree with Node[AndTree] {
    var minAlternative: Tree    = _
    def minCost: C              = minAlternative.minCost

    def computeMin = {
      if (!alternatives.isEmpty) {
        alternatives.values.minBy(_.minCost)
      } else {
        null
      }
    }

    def unsolvable(l: AndTree) {
      alternatives -= l.task

      if (alternatives.isEmpty) {
        parent.unsolvable(this)
      } else {
        minAlternative = computeMin
      }
    }

    def expandLeaf(l: AndLeaf, succ: List[OT]) {
      val n = AndNode(this, succ, l.task)
      n.subProblems = succ.map(t => t -> OrLeaf(n, t)).toMap
      n.minCost     = n.computeCost

      alternatives += l.task -> n
    }

    def notifySolution(sub: AndTree, sol: S) {
      solution match {
        case Some(preSol) if (preSol.cost < sol.cost) =>
          solution       = Some(sol)
          minAlternative = sub

          parent.notifySolution(this, solution.get)
        case None =>
          solution       = Some(sol)
          minAlternative = sub

          parent.notifySolution(this, solution.get)
      }
    }
  }

  case class OrLeaf(parent: AndNode, task: OT) extends OrTree with Leaf {
    def expandWith(succ: List[AT]) {
      parent.expandLeaf(this, succ)
    }
  }
}

abstract class AndOrGraphSearch[AT <: AOAndTask[S], OT <: AOOrTask[S], S <: AOSolution](val g: AndOrGraph[AT, OT, S]) {
  import collection.mutable.PriorityQueue

  def nextLeaf: Option[g.Leaf] = {
    var c: g.Tree = g.tree
    var res: Option[g.Leaf] = None

    while(res.isEmpty) {
      c match {
        case l: g.Leaf =>
          res = Some(l)

        case an: g.AndNode =>
          c = an.subProblems.values.minBy(_.minCost)

        case on: g.OrNode =>
          c = on.minAlternative
      }
    }

    res
  }

  abstract class ExpandResult
  case class ExpandedAnd(sub: List[OT]) extends ExpandResult
  case class ExpandedOr(sub: List[AT]) extends ExpandResult
  case class ExpandSuccess(sol: S) extends ExpandResult
  case object ExpandFailure extends ExpandResult

  var continue = true

  def search = {
    while (!g.tree.isSolved && continue) {
      nextLeaf match {
        case Some(l) =>
          l match {
            case al: g.AndLeaf =>
              processLeaf(al) match {
                case ExpandedAnd(ls) =>
                  al.expandWith(ls)
                case r @ ExpandSuccess(sol) =>
                  al.parent.notifySolution(al, sol)
                case _ =>
                  al.parent.unsolvable(al)
              }
            case ol: g.OrLeaf =>
              processLeaf(ol) match {
                case ExpandedOr(ls) =>
                  ol.expandWith(ls)
                case r @ ExpandSuccess(sol) =>
                  ol.parent.notifySolution(ol, sol)
                case _ =>
                  ol.parent.unsolvable(ol)
              }
          }
        case None =>
          continue = false
      }
    }
  }

  def processLeaf(l: g.Leaf): ExpandResult
}
