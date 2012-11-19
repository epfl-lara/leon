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
  def composeSolution(sols: List[S]): S
  def cost: AOCost
}

trait AOSolution {
  def cost: AOCost
}


class AndOrGraph[T <: AOTask[S], S <: AOSolution](val root: T) {
  type C = AOCost

  var tree: Tree = RootNode

  trait Tree {
    val task  : T
    val parent: Node

    def minCost: C

    def isSolved: Boolean
    def isUnsolvable: Boolean
  }

  abstract class AndTree extends Tree
  abstract class OrTree extends Tree


  trait Leaf extends Tree with Ordered[Leaf] {
    val minCost: C = task.cost

    def compare(that: Leaf) = this.minCost.compare(that.minCost)

    def isSolved: Boolean = false
    def isUnsolvable: Boolean = false
    def expandWith(succ: List[T])
  }

  trait Node {
    def expandLeaf(l: Leaf, succ: List[T])
    def unsolvable(l: Tree)
    def notifySolution(sub: Tree, sol: S)

    var solution: Option[S] = None
    var isUnsolvable = false

    def isSolved: Boolean = solution.isDefined
  }

  case class AndNode(parent: OrNode, subTasks: List[T], task: T) extends AndTree with Node {
    var subProblems         = Map[T, OrTree]()
    var subSolutions        = Map[T, S]()

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

    def unsolvable(l: Tree) {
      isUnsolvable = true
      parent.unsolvable(this)
    }

    def expandLeaf(l: Leaf, succ: List[T]) {
      val n = OrNode(this, Map(), l.task)
      n.alternatives = succ.map(t => t -> AndLeaf(n, t)).toMap
      n.minAlternative = n.computeMin

      subProblems += l.task -> n
    }

    def notifySolution(sub: Tree, sol: S) {
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
    override def expandWith(succ: List[T]) {
      val n = new OrNode(null, Map(), task) {
        override def unsolvable(l: Tree) {
          alternatives -= l.task

          if (alternatives.isEmpty) {
            isUnsolvable = true
          } else {
            minAlternative = computeMin
          }
        }
      }

      n.alternatives = succ.map(t => t -> AndLeaf(n, t)).toMap
      n.minAlternative = n.computeMin

      tree = n
    }
  }

  case class AndLeaf(parent: OrNode, task: T) extends AndTree with Leaf {
    def expandWith(succ: List[T]) {
      parent.expandLeaf(this, succ)
    }

  }


  case class OrNode(parent: AndNode, var alternatives: Map[T, AndTree], task: T) extends OrTree with Node {
    var minAlternative: Tree    = _
    def minCost: C              = minAlternative.minCost

    def computeMin = {
      if (!alternatives.isEmpty) {
        alternatives.values.minBy(_.minCost)
      } else {
        null
      }
    }

    def unsolvable(l: Tree) {
      alternatives -= l.task

      if (alternatives.isEmpty) {
        isUnsolvable = true
        parent.unsolvable(this)
      } else {
        minAlternative = computeMin
      }
    }

    def expandLeaf(l: Leaf, succ: List[T]) {
      val n = AndNode(this, succ, l.task)
      n.subProblems = succ.map(t => t -> OrLeaf(n, t)).toMap
      n.minCost     = n.computeCost

      alternatives += l.task -> n
    }

    def notifySolution(sub: Tree, sol: S) {
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

  case class OrLeaf(parent: AndNode, task: T) extends OrTree with Leaf {
    def expandWith(succ: List[T]) {
      parent.expandLeaf(this, succ)
    }
  }
}

abstract class AndOrGraphSearch[T <: AOTask[S], S <: AOSolution](val g: AndOrGraph[T, S]) {
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
  case class Expanded(sub: List[T]) extends ExpandResult
  case class ExpandSuccess(sol: S) extends ExpandResult
  case object ExpandFailure extends ExpandResult

  var continue = true

  def search = {
    while (!g.tree.isSolved && continue && !g.tree.isUnsolvable) {
      nextLeaf match {
        case Some(l) =>
          processLeaf(l) match {
            case r @ Expanded(ls) =>
              l.expandWith(ls)
            case r @ ExpandSuccess(sol) =>
              l.parent.notifySolution(l, sol)
            case r @ ExpandFailure =>
              l.parent.unsolvable(l)
          }
        case None =>
          continue = false
      }
    }
  }

  def processLeaf(l: g.Leaf): ExpandResult
}
