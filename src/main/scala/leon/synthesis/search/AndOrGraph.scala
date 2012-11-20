package leon.synthesis.search

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

  class AndNode(val parent: OrNode, val subTasks: List[OT], val task: AT) extends AndTree with Node[OrTree] {
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
      val n = new OrNode(this, Map(), l.task)
      n.alternatives = succ.map(t => t -> new AndLeaf(n, t)).toMap
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
      val n = new OrNode(null, Map(), root)
      n.alternatives = succ.map(t => t -> new AndLeaf(n, t)).toMap
      n.minAlternative = n.computeMin

      tree = n
    }
  }

  class AndLeaf(val parent: OrNode, val task: AT) extends AndTree with Leaf {
    def expandWith(succ: List[OT]) {
      parent.expandLeaf(this, succ)
    }

  }


  class OrNode(val parent: AndNode, var alternatives: Map[AT, AndTree], val task: OT) extends OrTree with Node[AndTree] {
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
      val n = new AndNode(this, succ, l.task)
      n.subProblems = succ.map(t => t -> new OrLeaf(n, t)).toMap
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

  class OrLeaf(val parent: AndNode, val task: OT) extends OrTree with Leaf {
    def expandWith(succ: List[AT]) {
      parent.expandLeaf(this, succ)
    }
  }
}

