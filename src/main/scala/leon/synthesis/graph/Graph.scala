/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package graph

import leon.utils.StreamUtils.cartesianProduct
import leon.utils.DebugSectionSynthesis

sealed class Graph(problem: Problem) {
  val root = new RootNode(problem)

  // Returns closed/total
  def getStats(from: Node = root): (Int, Int) = {
    val isClosed = from.isDeadEnd || from.isSolved
    val self = (if (isClosed) 1 else 0, 1)

    if (!from.isExpanded) {
      self
    } else {
      from.descendants.foldLeft(self) {
        case ((c,t), d) =>
          val (sc, st) = getStats(d)
          (c+sc, t+st)
      }
    }
  }
}

sealed abstract class Node(val parent: Option[Node]) extends Printable {

  var descendants: List[Node] = Nil
  // indicates whether this particular node has already been expanded
  var isExpanded: Boolean = false

  def expand(implicit hctx: SearchContext)

  val p: Problem

  var isSolved: Boolean   = false
  def onSolved(desc: Node)

  // Solutions this terminal generates (!= None for terminals)
  var solutions: Option[Stream[Solution]] = None
  var selectedSolution = -1

  var isDeadEnd: Boolean = false

  def isOpen = !isDeadEnd && !isSolved

  // For non-terminals, selected children for solution
  var selected: List[Node] = Nil

  def composeSolutions(sols: List[Stream[Solution]]): Stream[Solution]

  // Generate solutions given selection+solutions
  def generateSolutions(): Stream[Solution] = {
    solutions.getOrElse {
      composeSolutions(selected.map(n => n.generateSolutions()))
    }
  }
}

/** Represents the conjunction of search nodes.
  * @param parent Some node. None if it is the root node.
  * @param ri The rule instantiation that created this AndNode.
  **/
class AndNode(parent: Option[Node], val ri: RuleInstantiation) extends Node(parent) {
  val p = ri.problem

  override def asString(implicit ctx: LeonContext) = "\u2227 "+ri.asString

  def expand(implicit hctx: SearchContext): Unit = {
    require(!isExpanded)
    isExpanded = true

    def pad(prefix: String, message: String): String = {
      val lines = message.split("\\n").toList
      val padding = " " * (prefix.length + 1)
      prefix + " " + lines.head + "\n" + lines.tail.map(padding + _).mkString("\n")
    }

    import hctx.reporter.info

    val prefix = f"[${Option(ri).map(_.asString).getOrElse("?")}%-20s]"

    info(pad(prefix, ri.problem.asString))

    ri.apply(hctx) match {
      case RuleClosed(sols) =>
        solutions = Some(sols)
        selectedSolution = 0

        isSolved = sols.nonEmpty

        if (sols.isEmpty) {
          info(s"$prefix Failed")
          isDeadEnd = true
        } else {
          val sol = sols.head
          val morePrefix = s"$prefix Solved ${if(sol.isTrusted) "" else "(untrusted)"} with: "
          info(pad(morePrefix, sol.asString))
        }

        parent.foreach{ p =>
          if (isSolved) {
            p.onSolved(this)
          }
        }

      case RuleExpanded(probs) =>
        info(s"$prefix Decomposed into:")
        val morePrefix = s"$prefix -"
        for(p <- probs) { 
          info(pad(morePrefix, p.asString))
        }

        descendants = probs.map(p => new OrNode(Some(this), p))

        if (descendants.isEmpty) {
          isDeadEnd = true
        }

        selected = descendants
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
    if (solveds.size == descendants.size) {
      isSolved = true
      parent.foreach(_.onSolved(this))
    }
  }

}

class OrNode(parent: Option[Node], val p: Problem) extends Node(parent) {

  override def asString(implicit ctx: LeonContext) = "\u2228 "+p.asString

  implicit val debugSection = DebugSectionSynthesis
  
  def getInstantiations(hctx: SearchContext): List[RuleInstantiation] = {
    val rules = hctx.settings.rules

    val rulesPrio = rules.groupBy(_.priority).toSeq.sortBy(_._1)

    for ((prio, rs) <- rulesPrio) {
      
      val results = rs.flatMap{ r =>
        hctx.reporter.ifDebug(printer => printer("Testing rule: " + r))
        hctx.timers.synthesis.instantiations.get(r.asString(hctx)).timed {
          r.instantiateOn(hctx, p)
        }
      }.toList

      if (results.nonEmpty) {
        // We want to force all NormalizingRule's anyway, so no need to branch out.
        // Just force the first one, and the rest may be applied afterwards.
        return if (prio == RulePriorityNormalizing) results.take(1) else results
      }
    }

    Nil
  }

  def expand(implicit hctx: SearchContext): Unit = {
    require(!isExpanded)

    val ris = getInstantiations(hctx)

    descendants = ris.map(ri => new AndNode(Some(this), ri))
    selected = List()

    isExpanded = true
  }

  def onSolved(desc: Node): Unit = {
    isSolved = true
    selected = List(desc)
    parent.foreach(_.onSolved(this))
  }

  def composeSolutions(solss: List[Stream[Solution]]): Stream[Solution] = {
    solss.toStream.flatten
  }
}

class RootNode(p: Problem) extends OrNode(None, p)
