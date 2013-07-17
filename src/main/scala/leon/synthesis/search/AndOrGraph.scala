/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.search

trait AOTask[S] { }

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

  object LeafOrdering extends Ordering[Leaf] {
    def compare(a: Leaf, b: Leaf) = {
      val diff = scala.math.Ordering.Iterable[Int].compare(a.minReachCost, b.minReachCost)
      if (diff == 0) {
        if (a == b) {
          0
        } else {
          a.## - b.##
        }
      } else {
        diff
      }
    }
  }

  val leaves = collection.mutable.TreeSet()(LeafOrdering)
  leaves += RootNode

  trait Tree {
    val task : AOTask[S]
    val parent: Node[_]

    def minCost: Cost

    var minReachCost = List[Int]()

    def updateMinReach(reverseParent: List[Int]);
    def removeLeaves();

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
    val minCost = costModel.taskCost(task)

    var removedLeaf = false;

    def updateMinReach(reverseParent: List[Int]) {
      if (!removedLeaf) {
        leaves -= this
        minReachCost = (minCost.value :: reverseParent).reverse
        leaves += this
      }
    }

    def removeLeaves() {
      removedLeaf = true
      leaves -= this
    }
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
        if (parent ne null) {
            parent.updateMin()
        } else {
            // Reached the root, propagate minReach up
            updateMinReach(Nil)
        }
      } else {
        // Reached boundary of update, propagate minReach up
        updateMinReach(minReachCost.reverse.tail)
      }
    }

    def updateMinReach(reverseParent: List[Int]) {
      val rev = minCost.value :: reverseParent

      minReachCost = rev.reverse

      subProblems.values.foreach(_.updateMinReach(rev))
    }

    def removeLeaves() {
      subProblems.values.foreach(_.removeLeaves())
    }

    def unsolvable(l: OrTree) {
      isUnsolvable = true

      this.removeLeaves()

      parent.unsolvable(this)
    }

    def expandLeaf(l: OrLeaf, succ: List[AT]) {
      //println("[[2]] Expanding "+l.task+" to: ")
      //for (t <- succ) {
      //  println(" - "+t)
      //}

      //println("BEFORE: In leaves we have: ")
      //for (i <- leaves.iterator) {
      //  println("-> "+i.minReachCost+" == "+i.task)
      //}

      if (!l.removedLeaf) {
        l.removeLeaves()

        val orNode = new OrNode(this, succ, l.task)
        subProblems += l.task -> orNode

        updateMin()

        leaves ++= orNode.andLeaves.values
      }

      //println("AFTER: In leaves we have: ")
      //for (i <- leaves.iterator) {
      //  println("-> "+i.minReachCost+" == "+i.task)
      //}
    }

    def notifySolution(sub: OrTree, sol: S) {
      subSolutions += sub.task -> sol

      sub match {
        case l: Leaf =>
          l.removeLeaves()
        case _ =>
      }

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

    minReachCost = List(minCost.value)

    override def expandWith(succ: List[AT]) {
      this.removeLeaves()

      val orNode = new OrNode(null, succ, root)
      tree = orNode

      leaves ++= orNode.andLeaves.values
    }
  }

  class AndLeaf(val parent: OrNode, val task: AT) extends AndTree with Leaf {
    def expandWith(succ: List[OT]) {
      parent.expandLeaf(this, succ)
    }

  }


  class OrNode(val parent: AndNode, val altTasks: List[AT], val task: OT) extends OrTree with Node[AndTree] {
    val andLeaves                      = altTasks.map(t => t -> new AndLeaf(this, t)).toMap
    var alternatives: Map[AT, AndTree] = andLeaves
    var triedAlternatives              = Map[AT, AndTree]()
    var minAlternative: AndTree        = _
    var minCost                        = costModel.taskCost(task)

    updateMin()

    def updateMin() {
      if (!alternatives.isEmpty) {
        minAlternative = alternatives.values.minBy(_.minCost)
        val old = minCost 
        minCost        = minAlternative.minCost

        //println("Updated minCost of "+task+" from "+old.value+" to "+minCost.value)
        
        if (minCost != old) {
          if (parent ne null) {
            parent.updateMin()
          } else {
            // reached root, propagate minReach up
            updateMinReach(Nil)
          }
        } else {
          updateMinReach(minReachCost.reverse.tail)
        }
      } else {
        minAlternative = null
        minCost        = Cost.zero
      }
    }

    def updateMinReach(reverseParent: List[Int]) {
      val rev = minCost.value :: reverseParent

      minReachCost = rev.reverse

      alternatives.values.foreach(_.updateMinReach(rev))
    }

    def removeLeaves() {
      alternatives.values.foreach(_.removeLeaves())
    }

    def unsolvable(l: AndTree) {
      if (alternatives contains l.task) {
        triedAlternatives += l.task -> alternatives(l.task)
        alternatives -= l.task

        l.removeLeaves()

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
      //println("[[1]] Expanding "+l.task+" to: ")
      //for (t <- succ) {
      //  println(" - "+t)
      //}

      //println("BEFORE: In leaves we have: ")
      //for (i <- leaves.iterator) {
      //  println("-> "+i.minReachCost+" == "+i.task)
      //}

      if (!l.removedLeaf) {
        l.removeLeaves()

        val n = new AndNode(this, succ, l.task)

        val newLeaves = succ.map(t => t -> new OrLeaf(n, t)).toMap
        n.subProblems = newLeaves

        alternatives += l.task -> n

        n.updateMin()

        updateMin()

        leaves  ++= newLeaves.values
      }


      //println("AFTER: In leaves we have: ")
      //for (i <- leaves.iterator) {
      //  println("-> "+i.minReachCost+" == "+i.task)
      //}
    }

    def notifySolution(sub: AndTree, sol: S) {
      this.removeLeaves()

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

