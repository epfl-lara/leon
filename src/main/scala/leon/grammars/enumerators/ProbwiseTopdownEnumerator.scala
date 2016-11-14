package leon
package grammars
package enumerators

import purescala.Expressions.Expr

class ProbwiseTopdownEnumerator(protected val grammar: ExpressionGrammar, init: Label)(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr]
  with GrammarEnumerator
{
  val hors = GrammarEnumerator.horizonMap(init, productions).mapValues(_._2)
  protected def productions(nt: Label) = grammar.getProductions(nt)
  protected def nthor(nt: Label): Double = hors(nt)
}

abstract class AbstractProbwiseTopdownEnumerator[NT, R] {

  protected def productions(nt: NT): Seq[ProductionRule[NT, R]]

  protected def nthor(nt: NT): Double

  /**
    * Represents an element of the worklist
    *
    * @param expansion The partial expansion under consideration
    * @param logProb The log probability already accumulated by the expansion
    * @param horizon The minimum cost that this expansion will accumulate before becoming concrete
    */
  case class WorklistElement(
    expansion: Expansion[NT, R],
    logProb: Double,
    horizon: Double
  ) {
    require(logProb <= 0 && horizon <= 0)

    def get = expansion.produce
  }

  def iterator(nt: NT): Iterator[R] = new Iterator[R] {
    val ordering = Ordering.by[WorklistElement, Double](elem => elem.logProb + elem.horizon)
    val worklist = new scala.collection.mutable.PriorityQueue[WorklistElement]()(ordering)

    worklist.enqueue(new WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt)))
    var lastPrint: Int = 1
    var prevAns = new WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt))

    def hasNext: Boolean = worklist.nonEmpty

    def next: R = {
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
      assert(ans.logProb - 1.0e-6 <= prevAns.logProb)
      assert(ans.horizon >= -1.0e-6)
      prevAns = ans
      ans.get
    }

  }

  def expandNext(elem: WorklistElement): Seq[WorklistElement] = {
    val expansion = elem.expansion

    require(!expansion.complete)

    expansion match {

      case NonTerminalInstance(nt) =>
        val prodRules = productions(nt)
        for (rule <- prodRules) yield {
          val expansion = ProdRuleInstance(
            nt,
            rule,
            rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList
          )
          val logProbPrime = elem.logProb + rule.weight
          val horizonPrime = rule.subTrees.map(nthor).sum
          WorklistElement(expansion, logProbPrime, horizonPrime)
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
            yield (csHdExp.expansion :: csTl, csHdExp.logProb)
        }

        for (childExpansion <- expandChildren(children)) yield {
          val expPrime = ProdRuleInstance(nt, rule, childExpansion._1)
          val logProbPrime = elem.logProb + childExpansion._2
          val horizonPrime = expPrime.horizon(nthor)
          WorklistElement(expPrime, logProbPrime, horizonPrime)
        }
    }

  }
}
