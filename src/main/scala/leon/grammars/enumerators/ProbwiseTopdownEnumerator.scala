package leon
package grammars
package enumerators

import leon.grammars.enumerators.CandidateScorer.Score
import leon.synthesis.{Example, SynthesisPhase}
import purescala.Expressions.Expr
import scala.collection.mutable

class ProbwiseTopdownEnumerator(
    protected val grammar: ExpressionGrammar,
    init: Label,
    scorer: CandidateScorer[Label, Expr],
    examples: Seq[Example],
    eval: (Expr, Example) => Option[Expr],
    disambiguate: Boolean
  )(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr](scorer, disambiguate)
  with GrammarEnumerator
{
  val hors = GrammarEnumerator.horizonMap(init, productions).mapValues(_._2)
  protected def productions(nt: Label) = grammar.getProductions(nt)
  protected def nthor(nt: Label): Double = hors(nt)

  def sig(r: Expr): Option[Seq[Expr]] = {
    examples mapM (eval(r, _))
  }

}

object EnumeratorStats {
  var partialEvalAcceptCount: Int = 0
  var partialEvalRejectionCount: Int = 0
  var expandNextCallCount: Int = 0
  var iteratorNextCallCount: Int = 0
  var cegisIterCount: Int = 0
}

abstract class AbstractProbwiseTopdownEnumerator[NT, R](scorer: CandidateScorer[NT, R], disambiguate: Boolean)(implicit ctx: LeonContext) {

  import ctx.reporter._

  implicit protected val debugSection = leon.utils.DebugSectionSynthesis

  protected def productions(nt: NT): Seq[ProductionRule[NT, R]]

  protected def nthor(nt: NT): Double

  protected val coeff = ctx.findOptionOrDefault(SynthesisPhase.optProbwiseTopdownCoeff)

  protected val sigToNormalExp = mutable.Map[(NT, Sig), Expansion[NT, R]]()

  type Sig = Seq[R]

  def sig(r: R): Option[Sig]

  protected def isClassRepresentative(e: Expansion[NT, R]): Boolean =
    !disambiguate || !e.complete || {
      sig(e.produce).exists { theSig =>
        sigToNormalExp.get(e.nt, theSig) match {
          case None =>
            sigToNormalExp += (e.nt, theSig) -> e
            true
          case Some(`e`) =>
            true
          case _ =>
            false
        }
      }
    }

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

    def priorityExplanation = {
      val t1 = coeff * Math.log((score.nYes + 1.0) / (score.nExs + 1.0))
      val t2 = logProb + horizon
      Map("Priority" -> (t1 + t2),
          "nYes" -> score.nYes,
          "nExs" -> score.nExs,
          "t1" -> t1,
          "logProb" -> logProb,
          "horizon" -> horizon,
          "t2" -> t2)
    }

    val priority = {
      val t1 = coeff * Math.log((score.nYes + 1.0) / (score.nExs + 1.0))
      val t2 = logProb + horizon
      t1 + t2
    }
  }

  def iterator(nt: NT): Iterator[R] = new Iterator[R] {
    val ordering = Ordering.by[WorklistElement, Double](_.priority)
    val worklist = new mutable.PriorityQueue[WorklistElement]()(ordering)

    val seedExpansion = NonTerminalInstance[NT, R](nt)
    val seedScore = scorer.score(seedExpansion, Set(), eagerReturnOnFalse = false)
    val worklistSeed = WorklistElement(seedExpansion, 0.0, nthor(nt), seedScore)

    var prevAns = worklistSeed
    worklist.enqueue(worklistSeed)

    var lastPrint: Int = 1

    def hasNext: Boolean = {
      prepareNext()
      worklist.nonEmpty
    }

    def next: R = {
      EnumeratorStats.iteratorNextCallCount += 1
      prepareNext()
      assert(worklist.nonEmpty)
      val ans = worklist.dequeue
      // assert(ans.logProb - 1.0e-6 <= prevAns.logProb)
      // assert(ans.horizon >= -1.0e-6)
      prevAns = ans
      ans.get
    }

    def prepareNext(): Unit = {
      def elemCompliesTests(elem: WorklistElement) = {
        val score = scorer.score(elem.expansion, elem.score.yesExs, eagerReturnOnFalse = false)
        score.noExs.isEmpty
      }

      while (worklist.nonEmpty && (!worklist.head.expansion.complete || !elemCompliesTests(worklist.head))) {
        val head = worklist.dequeue
        val headScore = scorer.score(head.expansion, head.score.yesExs, eagerReturnOnFalse = false)

        if (headScore.noExs.isEmpty) {
          val newElems = expandNext(head, headScore)
          worklist ++= newElems

          EnumeratorStats.partialEvalAcceptCount += 1
          ifDebug{ printer =>
            if (worklist.size >= 2 * lastPrint) {
              printer(s"Worklist size: ${worklist.size}")
              //printer(s"Worklist head: ${worklist.head.expansion.falseProduce()}")
              printer(s"Accept / reject ratio: ${EnumeratorStats.partialEvalAcceptCount} /" +
                s"${EnumeratorStats.partialEvalRejectionCount}")
              lastPrint = worklist.size
            }
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
        for {
          rule <- prodRules
          expansion = ProdRuleInstance(
            nt,
            rule,
            rule.subTrees.map(ntChild => NonTerminalInstance[NT, R](ntChild)).toList
          )
          if isClassRepresentative(expansion)
        } yield {
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
            for ((expansions, logProb) <- expandChildren(csTl)) yield (csHd :: expansions, logProb)
          case csHd :: csTl =>
            for {
              csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0, elemScore), elemScore)
              if isClassRepresentative(csHdExp.expansion)
            } yield {
              (csHdExp.expansion :: csTl, csHdExp.logProb)
            }
        }

        for {
          (expansions, logProb) <- expandChildren(children)
          expPrime = ProdRuleInstance(nt, rule, expansions)
          if isClassRepresentative(expPrime)
        } yield {
          val logProbPrime = elem.logProb + logProb
          val horizonPrime = expPrime.horizon(nthor)
          WorklistElement(expPrime, logProbPrime, horizonPrime, elemScore)
        }
    }
  }
}
