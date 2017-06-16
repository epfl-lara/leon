/* Copyright 2009-2017 EPFL, Lausanne */

package leon
package grammars
package enumerators

import java.util.concurrent.atomic.AtomicBoolean

import CandidateScorer.Score
import purescala.Expressions.Expr
import purescala.Common.FreshIdentifier
import synthesis.{Example, SynthesisPhase}
import utils.{DedupedPriorityQueue, NoPosition}
import evaluators.EvaluationResults._

import scala.annotation.tailrec
import scala.collection.mutable

object ProbwiseTopdownEnumerator {
  val ntWrap = (e: NonTerminalInstance[Label, Expr]) => {
    FreshIdentifier.forceId(Console.BOLD + e.nt.asString(LeonContext.empty) + Console.RESET, 0, e.nt.tpe).toVariable
  }
}

class ProbwiseTopdownEnumerator(protected val grammar: ExpressionGrammar,
                                init: Label,
                                scorer: CandidateScorer[Label, Expr],
                                examples: Seq[Example],
                                eval: (Expr, Example) => Result[Expr],
                                minLogProb: Double,
                                maxEnumerated: Int,
                                indistinguish: Boolean
                               )(implicit ctx: LeonContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr](
    scorer,
    minLogProb,
    maxEnumerated,
    indistinguish,
    ProbwiseTopdownEnumerator.ntWrap
  ) with GrammarEnumerator {

  import ctx.reporter._
  override protected implicit val debugSection = leon.utils.DebugSectionSynthesis

  debug(s"Creating ProbwiseTopdownEnumerator with indistinguish = $indistinguish")
  debug("Available examples:")
  examples foreach (ex => debug("  -" + ex))

  val hors = timers.horMap.timed{ GrammarEnumerator.horizonMap(init, productions).map{ case (k,v) => k -> v._2 } }
  protected def productions(nt: Label) = grammar.getProductions(nt)
  protected def nthor(nt: Label): Double = hors(nt)

  private def worstResult(results: Seq[Result[Expr]]): Result[Seq[Expr]] = {
    results.collectFirst{ case e@RuntimeError(_) => e }
      .orElse(results.collectFirst{case e@EvaluatorError(_) => e})
      .getOrElse(Successful(results.map(_.result.get)))
  }

  def sig(r: Expr): Result[Seq[Expr]] = timers.sig.timed {
    worstResult(examples map (eval(r, _)))
  }

}

abstract class AbstractProbwiseTopdownEnumerator[NT, R](scorer: CandidateScorer[NT, R],
                                                        minLogProb: Double,
                                                        maxEnumerated: Double,
                                                        indistinguish: Boolean,
                                                        ntWrap: NonTerminalInstance[NT, R] => R
                                                       )(implicit ctx: LeonContext) {

  require(minLogProb < 0.0)

  protected val interrupted: AtomicBoolean = new AtomicBoolean(false)

  def interrupt(): Unit = {
    interrupted.set(true)
  }

  def recoverInterrupt(): Unit = {
    interrupted.set(false)
  }

  import ctx.reporter._
  implicit protected val debugSection = leon.utils.DebugSectionSynthesis
  def verboseDebug(msg: => String) = {
    debug(msg)(leon.utils.DebugSectionSynthesisVerbose)
  }
  def ifVerboseDebug(body: (Any => Unit) => Any) = {
    ifDebug(NoPosition, body)(leon.utils.DebugSectionSynthesisVerbose)
  }

  val timers = ctx.timers.synthesis.applications.get("Prob. driven enum")

  protected def productions(nt: NT): Seq[ProductionRule[NT, R]]

  protected def nthor(nt: NT): Double

  protected val coeff = ctx.findOptionOrDefault(SynthesisPhase.optProbwiseTopdownCoeff)

  type Sig = Seq[R]

  var generated = 0
  //var output = 0

  // Filter out seen expressions

  // A map from a signature of running on examples to an expansion that matches.
  // We consider expansions with equal signature identical
  protected val sigToClassRep = mutable.Map[Sig, R]()
  // A map from an expansion to a representative that was found to be identical
  protected val expToNormalForm = mutable.Map[Expansion[NT, R], Expansion[NT, R]]()
  def expRedundant(e: Expansion[NT, R]) = expToNormalForm(e)

  /** Use indistinguishability heuristic on expressions by signature */

  // Return the signature of an expression
  def sig(r: R): Result[Sig]

  // Returns normalized version of e, or None if it fails
  protected def normalize(e: Expansion[NT, R]): Option[Expansion[NT, R]] = {
    import leon.utils.CollectionUtils.MutableMapUtils
    e match {
      case NonTerminalInstance(_) =>
        // non-terminal instances are incomplete, thus not normalizable
        Some(e)
      case pri@ProdRuleInstance(nt, rule, children) =>
        // If we have representative for this expression, return it
        expToNormalForm.orElseUpdate(e, {
          // Otherwise...
          // Lazily make a normalized version of this based on the normalized versions of its children
          lazy val fromNormalizedChildren = children.mapM(normalize)
          if (!e.complete) {
            // If e is not complete, we cannot compute signature,
            // so reconstructing from the normalized children is best we can do.
            //println(s"Incomplete. ${e.falseProduce(ntWrap)} -> ${fromNormalizedChildren.map(_.falseProduce(ntWrap))}")
            fromNormalizedChildren.map(ProdRuleInstance(nt, rule, _))
          } else {
            // If e is complete expression...

            // Calculate its signature
            sig(e.produce) match {
              case Successful(theSig) =>
                // Look up in the signature map for an expansion with the same signature
                // If not found, fromNormalizedChildren will be the representative for this class.
                // Add it to the map and return it
                sigToClassRep.orElseUpdate( theSig, {
                  //println(s"Update: ${(e.nt.asInstanceOf[Label].tpe, theSig)} -> ${fromNormalizedChildren.map(_.falseProduce(ntWrap))}")
                  fromNormalizedChildren.map { ch =>
                    rule.builder(ch.map(_.produce))
                  }
                }).map { r =>
                  ProdRuleInstance(nt, ProductionRule(Nil, _ => r, rule.tag, 1, pri.logProb), Nil) // cost = 1 is wrong but we don't use it
                }
              case RuntimeError(_) =>
                // Program fails due to runtime error, i.e. it is wrong
                None
              case EvaluatorError(_) =>
                // We could not complete evaluation due to partial expression.
                // Return original expression
                Some(e)

            }
          }
        })
    }
  }

  /**
    * Represents an element of the worklist
    *
    * @param expansion The partial expansion under consideration
    * @param logProb The log probability already accumulated by the expansion
    * @param horizon The minimum cost that this expansion will accumulate before becoming concrete
    */
  case class WorklistElement(expansion: Expansion[NT, R],
                             logProb: Double,
                             horizon: Double,
                             score: Score,
                             parent: Option[WorklistElement]) {
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
      val t1 = {
        if (score.nExs == 0)
          0
        else
          - coeff * ( 1 - score.nYes / score.nExs)
      }
      val t2 = logProb + horizon
      t1 + t2
    }

    def lineage: Seq[WorklistElement] = this +: parent.map(_.lineage).getOrElse(Nil)
  }

  def iterator(nt: NT): Iterator[R] = new Iterator[R] {
    val ordering = Ordering.by[WorklistElement, Double](_.priority)
    val worklist = new DedupedPriorityQueue[WorklistElement, Expansion[NT, R]](elem => elem.expansion)(ordering)

    val seedExpansion = NonTerminalInstance[NT, R](nt)
    val seedScore = scorer.score(seedExpansion, Set(), eagerReturnOnFalse = true)
    val worklistSeed = WorklistElement(seedExpansion, 0.0, nthor(nt), seedScore, None)

    worklist.enqueue(worklistSeed)

    def hasNext: Boolean = !interrupted.get() && {
      prepareNext()
      worklist.nonEmpty
    }

    def next: R = {
      //prepareNext()
      assert(worklist.nonEmpty)
      val res = worklist.dequeue()
      debug(s"Returned element: ${res.get}")
      ifVerboseDebug { printer =>
        printer("Printing lineage for returned element:")
        res.lineage.foreach { elem => printer(s"    ${elem.priority}: ${elem.expansion.falseProduce(ntWrap)}") }
      }
      res.get
    }

    @tailrec def prepareNext(): Unit = {
      if (worklist.nonEmpty) {
        val elem = worklist.head
        // @mk: DIRTY HACK! This will set the solution for us for the purpose of recursive calls
        //      to be later used by normalization
        lazy val score = scorer.score(elem.expansion, elem.score.yesExs, eagerReturnOnFalse = true)
        lazy val compliesTests = {
          score.noExs.isEmpty
        }

        if (elem.priority < minLogProb || generated > maxEnumerated) {
          // We exhausted our limit of log. prob. or enumerated programs. Clear all and fail.
          val reason = if (elem.priority < minLogProb) "low probability" else "number of programs"
          debug(s"Enumerator exhausted resource ($reason)")
          worklist.clear()
        } else if (!elem.expansion.complete || !compliesTests) {
          // The element has to be removed from the queue,
          // because one of two conditions holds:
          // 1) it is incomplete (i.e. needs further expansion),
          // 2) it fails some tests (i.e. needs to be dropped).

          // So, remove it!
          worklist.dequeue()
          generated += 1
          ifDebug(printer =>
            if ((generated & (generated-1)) == 0) {
              printer(s"generated = $generated")
              printer(s"Worklist size = ${worklist.size}")
            }
          )
          verboseDebug(s"Dequeued (${elem.priority}): ${elem.expansion.falseProduce(ntWrap)}")

          if (compliesTests) {
            // If it is possible that the expansions of elem lead somewhere ...
            // First normalize it!
            // @mk: Dirty hack: This relies on the previous call to scorer.score for recursive calls
            val normalExpansionOpt = if (indistinguish) normalize(elem.expansion) else Some(elem.expansion)
            normalExpansionOpt match {
              case Some(normalExpansion) =>
                val normalElem = WorklistElement(normalExpansion, elem.logProb, elem.horizon, elem.score, elem.parent)
                ifVerboseDebug { printer =>
                  if (elem.expansion != normalExpansion) {
                    printer(s"Normalized to: ${normalExpansion.falseProduce(ntWrap)}")
                  }
                }

                // Then compute its immediate descendants and put them back in the worklist
                val newElems = expandNext(normalElem, score)
                verboseDebug(s"Expanded ${newElems.size} more elems")
                worklist.enqueueAll(newElems)

                // And debug some
                ifVerboseDebug { printer =>
                  newElems foreach { e =>
                    printer(s"Enqueued (${e.priority}): ${e.expansion.falseProduce(ntWrap)}")
                  }
                }

              case None =>
                verboseDebug(elem.expansion.falseProduce(ntWrap) + " failed evaluation")
            }
          } else {
            // The element has failed partial evaluation ...
            ifVerboseDebug { printer =>
              val scoreTriple = (score.yesExs.size, score.noExs.size, score.maybeExs.size)
              printer(s"Element rejected. compliesTests = $compliesTests, scoreTriple = $scoreTriple.")
            }
          }
          // We dequeued an element, so we don't necessarily have an acceptable element
          // on the head of the queue. Call rec again.
          prepareNext()
        }
      }
    }

  }

  def expandNext(elem: WorklistElement, elemScore: Score): Seq[WorklistElement] = {
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
          expansionPreNormal = expToNormalForm.getOrElse(expansion, expansion)
          // expansionPreNormal = expansion
        } yield {
          //println(s"NORMAL ${expansion.falseProduce(ntWrap)} -> ${expansionPreNormal.falseProduce(ntWrap)}")
          val logProbPrime = elem.logProb + rule.logProb
          val horizonPrime = rule.subTrees.map(nthor).sum
          WorklistElement(expansionPreNormal, logProbPrime, horizonPrime, elemScore, Some(elem))
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
              csHdExp <- expandNext(WorklistElement(csHd, 0.0, 0.0, elemScore, None), elemScore)
              csHdExpPreNormal = expToNormalForm.getOrElse(csHdExp.expansion, csHdExp.expansion)
              // csHdExpPreNormal = csHdExp.expansion
            } yield {
              //println(s"NORMAL ${csHdExp.expansion.falseProduce(ntWrap)} -> ${csHdExpPreNormal.falseProduce(ntWrap)}")
              (csHdExpPreNormal :: csTl, csHdExp.logProb)
            }
        }

        for {
          (expansions, logProb) <- expandChildren(children)
          expPrime = ProdRuleInstance(nt, rule, expansions)
          expPrimePreNormal = expToNormalForm.getOrElse(expPrime, expPrime)
          // expPrimePreNormal = expPrime
        } yield {
          val logProbPrime = elem.logProb + logProb
          val horizonPrime = expPrimePreNormal.horizon(nthor)
          WorklistElement(expPrimePreNormal, logProbPrime, horizonPrime, elemScore, Some(elem))
        }
    }
  }
}
