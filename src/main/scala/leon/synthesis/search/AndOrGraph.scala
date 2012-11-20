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
  var tree: OrTree = RootNode

  trait Tree {
    val task : AOTask[S]
    val parent: Node[_]

    def minCost: Cost

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
    def minCost = task.cost
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
          s.cost
        case _ =>
          val subCosts = subProblems.map { case (t, ot) => subSolutions.get(t).map(_.cost).getOrElse(ot.minCost) }

          subCosts.foldLeft(task.cost)(_ + _)
      }
      if (minCost != old) {
        Option(parent).foreach(_.updateMin())
      }
    }


    def unsolvable(l: OrTree) {
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
    var triedAlternatives    = Map[AT, AndTree]()
    var minAlternative: Tree = _
    var minCost              = Cost.zero

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

