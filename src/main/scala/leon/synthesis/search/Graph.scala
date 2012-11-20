package leon.synthesis.search

trait Cost extends Ordered[Cost] {
  def +(that: Cost): Cost = CostFixed(value + that.value)

  def value: Int

  def compare(that: Cost) = this.value - that.value
}

case class CostFixed(value: Int) extends Cost

object Cost {
  val zero = new CostFixed(0)
}

trait AOTask[S <: AOSolution] {
  def cost: Cost
}

trait AOAndTask[S <: AOSolution] extends AOTask[S] {
  def composeSolution(sols: List[S]): S
}

trait AOOrTask[S <: AOSolution] extends AOTask[S] {
}

trait AOSolution {
  def cost: Cost
}

class AndOrGraph[AT <: AOAndTask[S], OT <: AOOrTask[S], S <: AOSolution](val root: OT) {
  type C = Cost

  var tree: OrTree = RootNode

  trait Tree {
    val task : AOTask[S]
    val parent: Node[_]

    def minCost: C

    var solution: Option[S] = None

    def isSolved: Boolean = solution.isDefined
  }

  abstract class AndTree extends Tree {
    override val task: AT
  }

  abstract class OrTree extends Tree {
    override val task: OT

    def isUnsolvable: Boolean = false
  }


  trait Leaf extends Tree {
    def minCost: C = task.cost
  }

  trait Node[T <: Tree] extends Tree {
    def unsolvable(l: T)
    def notifySolution(sub: T, sol: S)

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

    def notifyParent(sol: S) {
      if (parent ne null) {
        parent.notifySolution(this, sol)
      }
    }
  }

  object RootNode extends OrLeaf(null, root) {

    override def expandWith(succ: List[AT]) {
      val n = OrNode(null, Map(), root)
      n.alternatives = succ.map(t => t -> AndLeaf(n, t)).toMap
      n.minAlternative = n.computeMin

      tree = n
    }
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

      minAlternative = computeMin
    }

    def notifySolution(sub: AndTree, sol: S) {
      solution match {
        case Some(preSol) if (preSol.cost < sol.cost) =>
          solution       = Some(sol)
          minAlternative = sub

          notifyParent(solution.get)
        case None =>
          solution       = Some(sol)
          minAlternative = sub

          notifyParent(solution.get)
      }
    }

    def notifyParent(sol: S) {
      if (parent ne null) {
        parent.notifySolution(this, sol)
      }
    }

    override def isUnsolvable: Boolean = alternatives.isEmpty
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
                  al.parent.notifySolution(al, sol)
                case _ =>
                  al.parent.unsolvable(al)
              }
            case ol: g.OrLeaf =>
              processOrLeaf(ol.task) match {
                case Expanded(ls) =>
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
    
    g.tree.solution
  }

  def processAndLeaf(l: AT): ExpandResult[OT]
  def processOrLeaf(l: OT): ExpandResult[AT]
}
