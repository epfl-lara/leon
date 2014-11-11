package leon
package synthesis
package graph

import leon.utils.StreamUtils.cartesianProduct

sealed class Graph(val cm: CostModel, problem: Problem) {
  val root = new RootNode(cm, problem)

  // Returns closed/total
  def getStats(from: Node = root): (Int, Int) = {
    val isClosed = from.isClosed || from.isSolved
    val self = (if (isClosed) 1 else 0, 1)

    if (!from.isExpanded) {
      self
    } else {
      from.descendents.foldLeft(self) {
        case ((c,t), d) =>
          val (sc, st) = getStats(d)
          (c+sc, t+st)
      }
    }
  }
}

sealed abstract class Node(cm: CostModel, parent: Option[Node]) {
  var parents: List[Node] = parent.toList
  var descendents: List[Node] = Nil

  // indicates whether this particular node has already been expanded
  var isExpanded: Boolean = false
  def expand(sctx: SynthesisContext)

  val p: Problem

  var isSolved: Boolean   = false


  def onSolved(desc: Node)

  // Solutions this terminal generates (!= None for terminals)
  var solutions: Option[Stream[Solution]] = None
  var selectedSolution = -1

  // Costs
  var cost: Cost = computeCost()

  def isClosed: Boolean = {
    cost.isImpossible
  }

  // For non-terminals, selected childs for solution
  var selected: List[Node] = Nil

  def composeSolutions(sols: List[Stream[Solution]]): Stream[Solution]

  // Generate solutions given selection+solutions
  def generateSolutions(): Stream[Solution] = {
    solutions.getOrElse {
      composeSolutions(selected.map(n => n.generateSolutions()))
    }
  }

  def computeCost(): Cost = solutions match {
    case Some(sols) if sols.isEmpty =>
      cm.impossible

    case Some(sols) =>
      sols.map { sol => cm.solution(sol) } .min

    case None =>
      val costs = if (isExpanded) {
        Some(descendents.map { _.cost })
      } else {
        None
      }

      this match {
        case an: AndNode =>
          cm.andNode(an, costs)

        case on: OrNode =>
          costs.map(_.min).getOrElse(cm.problem(on.p))
      }
  }

  def updateCost(): Unit = {
    cost = computeCost()
    parents.foreach(_.updateCost())
  }
}

class AndNode(cm: CostModel, parent: Option[Node], val ri: RuleInstantiation) extends Node(cm, parent) {
  val p = ri.problem

  override def toString = "\u2227 "+ri;

  def expand(sctx: SynthesisContext): Unit = {
    require(!isExpanded)
    isExpanded = true

    import sctx.reporter.info

    val prefix = "[%-20s] ".format(Option(ri.rule).getOrElse("?"))

    info(prefix+ri.problem)

    ri.apply(sctx) match {
      case RuleClosed(sols) =>
        solutions = Some(sols)
        selectedSolution = 0;

        updateCost()

        isSolved = sols.nonEmpty

        if (sols.isEmpty) {
          info(prefix+"Failed")
        } else {
          val sol = sols.head
          info(prefix+"Solved"+(if(sol.isTrusted) "" else " (untrusted)")+" with: "+sol+"...")
        }

        parents.foreach{ p =>
          p.updateCost()
          if (isSolved) {
            p.onSolved(this)
          }
        }

      case RuleExpanded(probs) =>
        info(prefix+"Decomposed into:")
        for(p <- probs) {
          info(prefix+"     - "+p)
        }

        descendents = probs.map(p => new OrNode(cm, Some(this), p))

        selected = descendents

        updateCost()
    }
  }

  def composeSolutions(solss: List[Stream[Solution]]): Stream[Solution] = {
    cartesianProduct(solss).flatMap {
      sols => ri.onSuccess(sols)
    }
  }

  private var solveds = Set[Node]()

  def onSolved(desc: Node): Unit = {
    // We store everything within solveds
    solveds += desc

    // Everything is solved correctly
    if (solveds.size == descendents.size) {
      isSolved = true;
      parents.foreach(_.onSolved(this))
    }
  }

}

class OrNode(cm: CostModel, parent: Option[Node], val p: Problem) extends Node(cm, parent) {

  override def toString = "\u2228 "+p;

  def expand(sctx: SynthesisContext): Unit = {
    require(!isExpanded)

    val ris = Rules.getInstantiations(sctx, p)

    descendents = ris.map(ri => new AndNode(cm, Some(this), ri))
    selected = List()

    updateCost()

    isExpanded = true
  }

  def onSolved(desc: Node): Unit = {
    isSolved = true
    selected = List(desc)
    parents.foreach(_.onSolved(this))
  }

  def composeSolutions(solss: List[Stream[Solution]]): Stream[Solution] = {
    solss.toStream.flatten
  }
}

class RootNode(cm: CostModel, p: Problem) extends OrNode(cm, None, p)
