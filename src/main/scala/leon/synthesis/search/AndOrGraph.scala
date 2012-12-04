package leon.synthesis.search

trait AOTask[S] {
}

trait AOAndTask[S] extends AOTask[S] {
  def composeSolution(sols: List[S]): S
}

trait AOOrTask[S] extends AOTask[S] {
}

trait AOCostModel[AT <: AOAndTask[S], OT <: AOOrTask[S], S] {
  def taskCost(at: AOTask[S]): Cost
  def solutionCost(s: S): Cost
}

class AndOrGraph[AT <: AOAndTask[S], OT <: AOOrTask[S], S](val root: OT, val costModel: AOCostModel[AT, OT, S]) {
  var tree: OrTree = RootNode

  trait Tree {
    val task : AOTask[S]
    val parent: Node[_]

    def minCost: Cost

    var solution: Option[S] = None
    var isUnsolvable: Boolean = false

    def isSolved: Boolean = solution.isDefined
  }

  abstract class AndTree extends Tree {
    override val task: AT
  }

  abstract class OrTree extends Tree {
    override val task: OT
  }


  trait Leaf extends Tree {
    def minCost = costModel.taskCost(task)
  }

  trait Node[T <: Tree] extends Tree {
    def unsolvable(l: T)
    def notifySolution(sub: T, sol: S)

  }

  class AndNode(val parent: OrNode, val subTasks: List[OT], val task: AT) extends AndTree with Node[OrTree] {
    var subProblems         = Map[OT, OrTree]()
    var subSolutions        = Map[OT, S]()

    var minCost = Cost.zero

    def updateMin() {
      val old = minCost
      minCost = solution match {
        case Some(s) =>
          costModel.solutionCost(s)
        case _ =>
          val subCosts = subProblems.values.map(_.minCost)

          subCosts.foldLeft(costModel.taskCost(task))(_ + _)
      }
      if (minCost != old) {
        Option(parent).foreach(_.updateMin())
      }
    }


    def unsolvable(l: OrTree) {
      isUnsolvable = true
      parent.unsolvable(this)
    }

    def expandLeaf(l: OrLeaf, succ: List[AT]) {
      val n = new OrNode(this, Map(), l.task)
      n.alternatives = succ.map(t => t -> new AndLeaf(n, t)).toMap
      n.updateMin()

      subProblems += l.task -> n
    }

    def notifySolution(sub: OrTree, sol: S) {
      subSolutions += sub.task -> sol

      if (subSolutions.size == subProblems.size) {
        solution = Some(task.composeSolution(subTasks.map(subSolutions)))
        updateMin()

        notifyParent(solution.get)
      } else {
        updateMin()
      }

    }

    def notifyParent(sol: S) {
      Option(parent).foreach(_.notifySolution(this, sol))
    }
  }

  object RootNode extends OrLeaf(null, root) {

    override def expandWith(succ: List[AT]) {
      val n = new OrNode(null, Map(), root)
      n.alternatives = succ.map(t => t -> new AndLeaf(n, t)).toMap
      n.updateMin()

      tree = n
    }
  }

  class AndLeaf(val parent: OrNode, val task: AT) extends AndTree with Leaf {
    def expandWith(succ: List[OT]) {
      parent.expandLeaf(this, succ)
    }

  }


  class OrNode(val parent: AndNode, var alternatives: Map[AT, AndTree], val task: OT) extends OrTree with Node[AndTree] {
    var triedAlternatives       = Map[AT, AndTree]()
    var minAlternative: AndTree = _
    var minCost                 = costModel.taskCost(task)

    def updateMin() {
      if (!alternatives.isEmpty) {
        minAlternative = alternatives.values.minBy(_.minCost)
        val old = minCost 
        minCost        = minAlternative.minCost
        if (minCost != old) {
          Option(parent).foreach(_.updateMin())
        }
      } else {
        minAlternative = null
        minCost        = Cost.zero
      }
    }

    def unsolvable(l: AndTree) {
      triedAlternatives += l.task -> alternatives(l.task)
      alternatives -= l.task


      if (alternatives.isEmpty) {
        isUnsolvable = true
        parent.unsolvable(this)
      } else {
        updateMin()
      }
    }

    def expandLeaf(l: AndLeaf, succ: List[OT]) {
      val n = new AndNode(this, succ, l.task)
      n.subProblems = succ.map(t => t -> new OrLeaf(n, t)).toMap
      n.updateMin()

      alternatives += l.task -> n

      updateMin()
    }

    def notifySolution(sub: AndTree, sol: S) {
      solution match {
        case Some(preSol) if (costModel.solutionCost(preSol) < costModel.solutionCost(sol)) =>
          solution       = Some(sol)
          minAlternative = sub

          notifyParent(solution.get)

        case None =>
          solution       = Some(sol)
          minAlternative = sub

          notifyParent(solution.get)

        case _ =>
      }
    }

    def notifyParent(sol: S) {
      if (parent ne null) {
        parent.notifySolution(this, sol)
      }
    }
  }

  class OrLeaf(val parent: AndNode, val task: OT) extends OrTree with Leaf {
    def expandWith(succ: List[AT]) {
      parent.expandLeaf(this, succ)
    }
  }
}

