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

}

case class NonTerminalInstance[NT, R](override val nt: NT) extends Expansion[NT, R](nt) {
  override val complete: Boolean = false
  override def produce: R = throw new NoSuchElementException(s"Unable to expand non-terminal ${this}")
  override val size: Int = 1
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

}

object Expansion {

  def expansionIterator[NT, R](
      nt: NT,
      grammar: NT => Seq[ProductionRule[NT, R]]
  ) = new Iterator[(Expansion[NT, R], Double)](){

    type TyEl = (Expansion[NT, R], Double)
    val ordering = Ordering.by[TyEl, Double](-_._2)
    val worklist = new scala.collection.mutable.PriorityQueue[TyEl]()(ordering)

    worklist.enqueue((NonTerminalInstance[NT, R](nt), 0.0))
    var lastPrint: Int = 1

    def hasNext: Boolean = worklist.nonEmpty

    def next: TyEl = {
      while (!worklist.head._1.complete) {
        val head = worklist.dequeue
        for (headNext <- expandNext(head._1, grammar)) {
          val newElem = (headNext._1, head._2 + headNext._2)
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
      expansion: Expansion[NT, R],
      grammar: NT => Seq[ProductionRule[NT, R]]
  ): Seq[(Expansion[NT, R], Double)] = {
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
          val minusLogProbPrime = logTotalWeight - Math.log(rule.weight)
          (expansion, minusLogProbPrime)
        }
      }

      case ProdRuleInstance(nt, rule, children) => {
        require(children.exists(!_.complete))

        def expandChildren(cs: List[Expansion[NT, R]]): Seq[(List[Expansion[NT, R]], Double)] = cs match {
          case Nil => throw new IllegalArgumentException()
          case csHd :: csTl if csHd.complete => for (csTlExp <- expandChildren(csTl))
                                                yield (csHd :: csTlExp._1, csTlExp._2)
          case csHd :: csTl => for (csHdExp <- expandNext(csHd, grammar))
                               yield (csHdExp._1 :: csTl, csHdExp._2)
        }
  
        for (childExpansion <- expandChildren(children)) yield {
          val expansion = ProdRuleInstance(nt, rule, childExpansion._1)
          (expansion, childExpansion._2)
        }
      }

    }
  }

}
