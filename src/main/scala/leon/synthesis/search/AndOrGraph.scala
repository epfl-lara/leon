package leon.synthesis.search

trait AOTask[S] {
}

trait AOAndTask[S] extends AOTask[S] {
  def composeSolution(sols: List[S]): Option[S]
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

    var isTrustworthy: Boolean = true
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
      subProblems += l.task -> new OrNode(this, succ, l.task)
    }

    def notifySolution(sub: OrTree, sol: S) {
      subSolutions += sub.task -> sol

      if (subSolutions.size == subProblems.size) {
        task.composeSolution(subTasks.map(subSolutions)) match {
          case Some(sol) =>
            isTrustworthy = subProblems.forall(_._2.isTrustworthy)
            solution = Some(sol)
            updateMin()

            notifyParent(sol)

          case None =>
            if (solution.isEmpty) {
              unsolvable(sub)
            }
        }
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
      tree = new OrNode(null, succ, root)
    }
  }

  class AndLeaf(val parent: OrNode, val task: AT) extends AndTree with Leaf {
    def expandWith(succ: List[OT]) {
      parent.expandLeaf(this, succ)
    }

  }


  class OrNode(val parent: AndNode, val altTasks: List[AT], val task: OT) extends OrTree with Node[AndTree] {
    var alternatives: Map[AT, AndTree] = altTasks.map(t => t -> new AndLeaf(this, t)).toMap
    var triedAlternatives              = Map[AT, AndTree]()
    var minAlternative: AndTree        = _
    var minCost                        = costModel.taskCost(task)

    updateMin()

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
      if (alternatives contains l.task) {
        triedAlternatives += l.task -> alternatives(l.task)
        alternatives -= l.task


        if (alternatives.isEmpty) {
          isUnsolvable = true
          if (parent ne null) {
            parent.unsolvable(this)
          }
        } else {
          updateMin()
        }
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
          isTrustworthy  = sub.isTrustworthy
          solution       = Some(sol)
          minAlternative = sub

          notifyParent(solution.get)

        case None =>
          isTrustworthy  = sub.isTrustworthy
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

  def getStatus: (Int, Int) = {
    var total: Int = 0
    var closed: Int = 0

    def tr(t: Tree, isParentClosed: Boolean) {
      val isClosed = isParentClosed || t.isSolved || t.isUnsolvable
      if (isClosed) {
        closed += 1
      }
      total += 1

      t match {
        case an: AndNode =>
          an.subProblems.values.foreach(tr(_, isClosed))
        case on: OrNode =>
          (on.alternatives.values ++ on.triedAlternatives.values).foreach(tr(_, isClosed))
        case _ =>
      }
    }

    tr(tree, false)

    (closed, total)
  }
}

