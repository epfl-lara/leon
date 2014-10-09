package leon
package synthesis
package graph

import leon.utils.StreamUtils.cartesianProduct

sealed class Graph(problem: Problem, costModel: CostModel) {
  type Cost = Int

  var maxCost = 100;

  val root = new RootNode(problem)

  sealed abstract class Node(parent: Option[Node]) {
    var parents: List[Node] = parent.toList
    var descendents: List[Node] = Nil

    // indicates whether this particular node has already been expanded
    var isExpanded: Boolean = false
    def expand(sctx: SynthesisContext)

    val p: Problem

    // costs
    var costDist: Distribution
    def onNewDist(desc: Node)

    var isSolved: Boolean   = false

    def isClosed: Boolean = {
      costDist.total == 0
    }

    def onSolved(desc: Node)

    // Solutions this terminal generates (!= None for terminals)
    var solutions: Option[Stream[Solution]] = None
    var selectedSolution = -1

    // For non-terminals, selected childs for solution
    var selected: List[Node] = Nil

    def composeSolutions(sols: List[Stream[Solution]]): Stream[Solution]

    // Generate solutions given selection+solutions
    def generateSolutions(): Stream[Solution] = {
      solutions.getOrElse {
        composeSolutions(selected.map(n => n.generateSolutions()))
      }
    }
  }

  class AndNode(parent: Option[Node], val ri: RuleInstantiation) extends Node(parent) {
    val p = ri.problem
    var selfCost = Distribution.point(maxCost, costModel.ruleAppCost(ri))
    var costDist: Distribution = Distribution.uniformFrom(maxCost, costModel.ruleAppCost(ri), 0.5)

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

          costDist = sols.foldLeft(Distribution.empty(maxCost)) {
            (d, sol) => d or Distribution.point(maxCost, costModel.solutionCost(sol))
          }

          isSolved = sols.nonEmpty

          if (sols.isEmpty) {
            info(prefix+"Failed")
          } else {
            val sol = sols.head
            info(prefix+"Solved"+(if(sol.isTrusted) "" else " (untrusted)")+" with: "+sol+"...")
          }

          parents.foreach{ p =>
            p.onNewDist(this)
            if (isSolved) {
              p.onSolved(this)
            }
          }

        case RuleExpanded(probs) =>
          info(prefix+"Decomposed into:")
          for(p <- probs) {
            info(prefix+"     - "+p)
          }

          descendents = probs.map(p => new OrNode(Some(this), p))

          selected = descendents

          recomputeCost()
      }
    }

    def composeSolutions(solss: List[Stream[Solution]]): Stream[Solution] = {
      cartesianProduct(solss).flatMap {
        sols => ri.onSuccess(sols)
      }
    }

    def onNewDist(desc: Node) = {
      recomputeCost()
    }

    private def recomputeCost() = {
      val newCostDist = descendents.foldLeft(selfCost){
        case (c, d)  => c and d.costDist
      }

      if (newCostDist != costDist) {
        costDist = newCostDist
        parents.foreach(_.onNewDist(this))
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

  class OrNode(parent: Option[Node], val p: Problem) extends Node(parent) {
    var costDist: Distribution = Distribution.uniformFrom(maxCost, costModel.problemCost(p), 0.5)

    override def toString = "\u2228 "+p;

    def expand(sctx: SynthesisContext): Unit = {
      require(!isExpanded)

      val ris = Rules.getInstantiations(sctx, p)

      descendents = ris.map(ri => new AndNode(Some(this), ri))
      selected = List()

      recomputeCost()

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

    private def recomputeCost(): Unit = {
      val newCostDist = descendents.foldLeft(Distribution.empty(maxCost)){
        case (c, d)  => c or d.costDist
      }

      if (costDist != newCostDist) {
        costDist = newCostDist
        parents.foreach(_.onNewDist(this))

      }
    }

    def onNewDist(desc: Node): Unit = {
      recomputeCost()
    }
  }

  class RootNode(p: Problem) extends OrNode(None, p)

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
