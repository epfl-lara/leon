package leon
package grammars

/**
 * Represents a (partial) expansion of the rules of the grammar
 * @param nt: Non-terminal being expanded at the head
 * @tparam NT The type of non-terminal symbols of the grammar
 * @tparam R The type of syntax trees of the grammar
 */
sealed abstract class Expansion[NT, R](val nt: NT) {

  /** Indicates whether the expansion is complete, or whether unexpanded non-terminals still exist. */
  def complete: Boolean

  /**
   * Produces the expansion.
   * @throws `NoSuchElementException` if the expansion is not complete
   */
  def produce: R

  /**
   * Size of the expansion
   */
  def size: Int

  /**
   * Computes the ``horizon'' of this partial expansion. The horizon is the minimum extra negative log probability of
   * all completed extensions of this expansion.
   * @param grammar The grammar
   * @param nthor The horizon of each non-terminal
   */
  def horizon(nthor: NT => Double): Double

}

case class NonTerminalInstance[NT, R](override val nt: NT) extends Expansion[NT, R](nt) {
  override val complete: Boolean = false
  override def produce: R = throw new NoSuchElementException(s"Unable to expand non-terminal ${this}")
  override val size: Int = 1
  override def horizon(nthor: NT => Double): Double = nthor(nt)
}

case class ProdRuleInstance[NT, R](
    override val nt: NT,
    rule: ProductionRule[NT, R],
    children: List[Expansion[NT, R]]
) extends Expansion[NT, R](nt) {

  require(children.map(_.nt) == rule.subTrees)
  override val complete: Boolean = children.forall(_.complete)
  override def produce: R = rule.builder(children.map(_.produce))
  override val size: Int = 1 + children.map(_.size).sum
  override def horizon(nthor: NT => Double): Double = children.map(c => c.horizon(nthor)).sum

}

object Expansion {

  /**
   * Represents an element of the worklist
   * @param expansion The partial expansion under consideration
   * @param cost The cost already accumulated by the expansion
   * @param horizon The minimum cost that this expansion will accumulate before becoming concrete
   */
  case class WorklistElement[NT, R](
      expansion: Expansion[NT, R],
      cost: Double,
      horizon: Double
  ) {
    require(cost >= 0 && horizon >= 0)
  }

  def expansionIterator[NT, R](
      nt: NT,
      grammar: NT => Seq[ProductionRule[NT, R]],
      nthor: NT => Double
  ) = new Iterator[WorklistElement[NT, R]](){

    type TyEl = WorklistElement[NT, R]
    val ordering = Ordering.by[TyEl, Double](elem => -(elem.cost + elem.horizon))
    val worklist = new scala.collection.mutable.PriorityQueue[TyEl]()(ordering)

    worklist.enqueue(new TyEl(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt)))
    var lastPrint: Int = 1

    def hasNext: Boolean = worklist.nonEmpty

    def next: TyEl = {
      while (!worklist.head.expansion.complete) {
        val head = worklist.dequeue
        // println(s"<< Dequeueing ${head}")
        for (newElem <- expandNext(head, grammar, nthor)) {
          worklist.enqueue(newElem)
          // println(s">> Enqueueing ${newElem}")

          if (worklist.size >= lastPrint + lastPrint) {
            println(s"Worklist size: ${worklist.size}")
            lastPrint = worklist.size
          }
        }
      }
      worklist.dequeue
    }

  }

  def expandNext[NT, R](
      elem: WorklistElement[NT, R],
      grammar: NT => Seq[ProductionRule[NT, R]],
      nthor: NT => Double
  ): Seq[WorklistElement[NT, R]] = {
    val expansion = elem.expansion
    val minusLogProb = elem.cost
    val horizon = elem.horizon

    require(!expansion.complete)

    expansion match {

      case NonTerminalInstance(nt) => {
        val prodRules = grammar(nt)
        val totalWeight = prodRules.map(_.weight).sum
        val logTotalWeight = Math.log(totalWeight)
        for (rule <- prodRules) yield {
          val expansion = ProdRuleInstance(nt,
                                           rule,
                                           rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList)
          val minusLogProbPrime = minusLogProb + logTotalWeight - Math.log(rule.weight)
          val horizonPrime = rule.subTrees.map(nthor).sum
          WorklistElement(expansion, minusLogProbPrime, horizonPrime)
        }
      }

      case ProdRuleInstance(nt, rule, children) => {
        require(children.exists(!_.complete))

        def expandChildren(cs: List[Expansion[NT, R]]): Seq[(List[Expansion[NT, R]], Double)] = cs match {
          case Nil => throw new IllegalArgumentException()
          case csHd :: csTl if csHd.complete => for (csTlExp <- expandChildren(csTl))
                                                yield (csHd :: csTlExp._1, csTlExp._2)
          case csHd :: csTl => for (csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0), grammar, nthor))
                               yield (csHdExp.expansion :: csTl, csHdExp.cost)
        }
  
        for (childExpansion <- expandChildren(children)) yield {
          val expansion = ProdRuleInstance(nt, rule, childExpansion._1)
          val minusLogProbPrime = minusLogProb + childExpansion._2
          val horizonPrime = expansion.horizon(nthor)
          WorklistElement[NT, R](expansion, minusLogProbPrime, horizon)
        }
      }

    }
  }

}
