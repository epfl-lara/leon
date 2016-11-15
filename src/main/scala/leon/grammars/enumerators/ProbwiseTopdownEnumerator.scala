package leon
package grammars
package enumerators

import purescala.Expressions.Expr

class ProbwiseTopdownEnumerator(
    protected val grammar: ExpressionGrammar,
    init: Label,
    scoreCandidate: Expansion[Label, Expr] => (Int, Int)
  )(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr](scoreCandidate)
  with GrammarEnumerator
{
  val hors = GrammarEnumerator.horizonMap(init, productions).mapValues(_._2)
  protected def productions(nt: Label) = grammar.getProductions(nt)
  protected def nthor(nt: Label): Double = hors(nt)
}

object EnumeratorStats {
  var partialEvalAcceptCount: Int = 0
  var partialEvalRejectionCount: Int = 0
  var expandNextCallCount: Int = 0
  var iteratorNextCallCount: Int = 0
  var cegisIterCount: Int = 0
}

abstract class AbstractProbwiseTopdownEnumerator[NT, R](
    scoreCandidate: Expansion[NT, R] => (Int, Int)
  )(implicit ctx: LeonContext) {

  import ctx.reporter._
  implicit val debugSection = leon.utils.DebugSectionSynthesis

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
    horizon: Double,
    score: Int
  ) {
    require(logProb <= 0 && horizon <= 0)

    def get = expansion.produce
  }

  def iterator(nt: NT): Iterator[(R, Double)] = new Iterator[(R, Double)] {
    val ordering = Ordering.by[WorklistElement, Double](elem => 8 * elem.score + elem.logProb + elem.horizon)
    val worklist = new scala.collection.mutable.PriorityQueue[WorklistElement]()(ordering)
    val worklistSeed = WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt), 0)
    var prevAns = worklistSeed

    worklist.enqueue(worklistSeed)

    var lastPrint: Int = 1

    def hasNext: Boolean = {
      while (worklist.nonEmpty && scoreCandidate(worklist.head.expansion)._2 > 0) {
        worklist.dequeue
      }
      worklist.nonEmpty
    }

    def next: (R, Double) = {
      EnumeratorStats.iteratorNextCallCount += 1
      while (!worklist.head.expansion.complete) {
        val head = worklist.dequeue
        val headScore = scoreCandidate(head.expansion) // (0, 0) to disable partial evaluation
        if (headScore._2 == 0) {
          EnumeratorStats.partialEvalAcceptCount += 1
          val newElems = expandNext(head, headScore._1)
          worklist ++= newElems
          if (worklist.size >= 1.5 * lastPrint) {
            debug(s"Worklist size: ${worklist.size}")
            debug("Accept / reject ratio: " +
                  s"${EnumeratorStats.partialEvalAcceptCount} /" +
                  s"${EnumeratorStats.partialEvalRejectionCount}")
            lastPrint = worklist.size
          }
        } else {
          EnumeratorStats.partialEvalRejectionCount += 1
        }
      }

      val ans = worklist.dequeue
      // assert(ans.logProb - 1.0e-6 <= prevAns.logProb)
      // assert(ans.horizon >= -1.0e-6)
      prevAns = ans
      (ans.get, ans.logProb)
    }

  }

  def expandNext(elem: WorklistElement, elemScore: Int): Seq[WorklistElement] = {
    EnumeratorStats.expandNextCallCount += 1
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
          WorklistElement(expansion, logProbPrime, horizonPrime, elemScore)
        }

      case ProdRuleInstance(nt, rule, children) =>
        require(children.exists(!_.complete))

        def expandChildren(cs: List[Expansion[NT, R]]): Seq[(List[Expansion[NT, R]], Double)] = cs match {
          case Nil =>
            throw new IllegalArgumentException()
          case csHd :: csTl if csHd.complete =>
            for (csTlExp <- expandChildren(csTl)) yield (csHd :: csTlExp._1, csTlExp._2)
          case csHd :: csTl =>
            for (csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0, 0), 0))
            yield (csHdExp.expansion :: csTl, csHdExp.logProb)
        }

        for (childExpansion <- expandChildren(children)) yield {
          val expPrime = ProdRuleInstance(nt, rule, childExpansion._1)
          val logProbPrime = elem.logProb + childExpansion._2
          val horizonPrime = expPrime.horizon(nthor)
          WorklistElement(expPrime, logProbPrime, horizonPrime, elemScore)
        }
    }

  }
}
