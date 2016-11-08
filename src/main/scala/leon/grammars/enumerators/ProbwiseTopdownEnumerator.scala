package leon
package grammars
package enumerators

import purescala.Expressions.Expr

class ProbwiseTopdownEnumerator(protected val grammar: ExpressionGrammar)(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr]
  with GrammarEnumerator
{
  protected def productions(nt: Label) = grammar.getProductions(nt)
}

abstract class AbstractProbwiseTopdownEnumerator[NT, R] {

  protected def productions(nt: NT): Seq[ProductionRule[NT, R]]

  protected def nthor(nt: NT): Double = Math.log(productions(nt).size)

  /**
    * Represents an element of the worklist
    *
    * @param expansion The partial expansion under consideration
    * @param cost The cost already accumulated by the expansion
    * @param horizon The minimum cost that this expansion will accumulate before becoming concrete
    */
  case class WorklistElement(
    expansion: Expansion[NT, R],
    cost: Double,
    horizon: Double
  ) {
    require(cost >= 0 && horizon >= 0)

    def get = expansion.produce
  }

  def iterator(nt: NT) = new Iterator[(R, Double)](){
    val ordering = Ordering.by[WorklistElement, Double](elem => -(elem.cost + elem.horizon))
    val worklist = new scala.collection.mutable.PriorityQueue[WorklistElement]()(ordering)

    worklist.enqueue(new WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt)))
    var lastPrint: Int = 1
    var prevAns = new WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt))

    def hasNext: Boolean = worklist.nonEmpty

    def next: (R, Double) = {
      while (!worklist.head.expansion.complete) {
        val head = worklist.dequeue
        val newElems = expandNext(head)
        worklist ++= newElems
        if (worklist.size >= 1.5 * lastPrint) {
          //println(s"Worklist size: ${worklist.size}")
          lastPrint = worklist.size
        }
      }

      val ans = worklist.dequeue
      assert(ans.cost + 1.0e-6 >= prevAns.cost)
      assert(ans.horizon <= 1.0e-6)
      prevAns = ans
      (ans.get, ans.cost)
    }

  }

  def expandNext(elem: WorklistElement): Seq[WorklistElement] = {
    val expansion = elem.expansion
    val minusLogProb = elem.cost

    require(!expansion.complete)

    expansion match {

      case NonTerminalInstance(nt) =>
        val prodRules = productions(nt)
        // val totalWeight = prodRules.map(_.weight).sum
        // val logTotalWeight = Math.log(totalWeight)
        for (rule <- prodRules) yield {
          val expansion = ProdRuleInstance(
            nt,
            rule,
            rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList
          )
          val minusLogProbPrime = minusLogProb - rule.weight
          val horizonPrime = rule.subTrees.map(nthor).sum
          WorklistElement(expansion, minusLogProbPrime, horizonPrime)
        }

      case ProdRuleInstance(nt, rule, children) =>
        require(children.exists(!_.complete))

        def expandChildren(cs: List[Expansion[NT, R]]): Seq[(List[Expansion[NT, R]], Double)] = cs match {
          case Nil =>
            throw new IllegalArgumentException()
          case csHd :: csTl if csHd.complete =>
            for (csTlExp <- expandChildren(csTl)) yield (csHd :: csTlExp._1, csTlExp._2)
          case csHd :: csTl =>
            for (csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0)))
            yield (csHdExp.expansion :: csTl, csHdExp.cost)
        }

        for (childExpansion <- expandChildren(children)) yield {
          val expPrime = ProdRuleInstance(nt, rule, childExpansion._1)
          val minusLogProbPrime = minusLogProb + childExpansion._2
          val horizonPrime = expPrime.horizon(nthor)
          WorklistElement(expPrime, minusLogProbPrime, horizonPrime)
        }
    }

  }
}
