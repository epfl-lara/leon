package leon
package grammars
package enumerators

import leon.grammars.enumerators.CandidateScorer.Score
import purescala.Expressions.Expr

class ProbwiseTopdownEnumerator(
    protected val grammar: ExpressionGrammar,
    init: Label,
    scorer: CandidateScorer[Expr]
  )(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr](scorer)
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

abstract class AbstractProbwiseTopdownEnumerator[NT, R](scorer: CandidateScorer[R])(implicit ctx: LeonContext) {

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
    score: Score
  ) {
    require(logProb <= 0 && horizon <= 0)
    def get = expansion.produce
    val yesScore = score.nYes
    // val priority = 8 * yesScore + logProb + horizon
    val priority = {
      val t1 = 16 * Math.log((score.nYes + 1.0) / (score.nExs + 1.0))
      val t2 = logProb + horizon
      t1 + t2
    }
  }

  def iterator(nt: NT): Iterator[(R, Double)] = new Iterator[(R, Double)] {
    val ordering = Ordering.by[WorklistElement, Double](_.priority)
    val worklist = new scala.collection.mutable.PriorityQueue[WorklistElement]()(ordering)

    val worklistSeed = WorklistElement(NonTerminalInstance[NT, R](nt), 0.0, nthor(nt), CandidateScorer.SEED_SCORE)
    var prevAns = worklistSeed
    worklist.enqueue(worklistSeed)

    var lastPrint: Int = 1

    def hasNext: Boolean = {
      prepareNext()
      worklist.nonEmpty
    }

    def next: (R, Double) = {
      EnumeratorStats.iteratorNextCallCount += 1
      prepareNext()
      assert(worklist.nonEmpty)
      val ans = worklist.dequeue
      // assert(ans.logProb - 1.0e-6 <= prevAns.logProb)
      // assert(ans.horizon >= -1.0e-6)
      prevAns = ans
      (ans.get, ans.logProb)
    }

    def prepareNext(): Unit = {
      while (worklist.nonEmpty && !worklist.head.expansion.complete) {
        val head = worklist.dequeue
        val headScore = scorer.score(head.expansion, head.score.maybeExs, eagerReturnOnFalse = false)
        if (headScore.noExs.isEmpty) {
          val newElems = expandNext(head, headScore)
          worklist ++= newElems

          EnumeratorStats.partialEvalAcceptCount += 1
          if (worklist.size >= 1.5 * lastPrint) {
            debug(s"Worklist size: ${worklist.size}")
            debug(s"Accept / reject ratio: ${EnumeratorStats.partialEvalAcceptCount} /" +
              s"${EnumeratorStats.partialEvalRejectionCount}")
            lastPrint = worklist.size
          }
        } else {
          EnumeratorStats.partialEvalRejectionCount += 1
        }
      }
    }

  }

  def expandNext(elem: WorklistElement, elemScore: Score): Seq[WorklistElement] = {
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
            for (csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0, elemScore), elemScore))
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
