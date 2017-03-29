/* Copyright 2009-2017 EPFL, Lausanne */

package leon
package grammars
package enumerators

import CandidateScorer.Score
import purescala.Expressions.Expr
import purescala.Common.FreshIdentifier
import synthesis.{Example, SynthesisContext, SynthesisPhase}
import utils.{DedupedPriorityQueue, NoPosition}

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
                                eval: (Expr, Example) => Option[Expr],
                                minLogProb: Double,
                                disambiguate: Boolean
                               )(implicit sctx: SynthesisContext)
  extends AbstractProbwiseTopdownEnumerator[Label, Expr](
    scorer,
    minLogProb,
    disambiguate,
    ProbwiseTopdownEnumerator.ntWrap
  ) with GrammarEnumerator {

  import sctx.reporter._
  override protected implicit val debugSection = leon.utils.DebugSectionSynthesis

  debug(s"Creating ProbwiseTopdownEnumerator with disambiguate = $disambiguate")

  val hors = GrammarEnumerator.horizonMap(init, productions).map{ case (k,v) => k -> v._2 }
  protected def productions(nt: Label) = grammar.getProductions(nt)
  protected def nthor(nt: Label): Double = hors(nt)

  def sig(r: Expr): Option[Seq[Expr]] = timers.sig.timed {
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

abstract class AbstractProbwiseTopdownEnumerator[NT, R](scorer: CandidateScorer[NT, R],
                                                        minLogProb: Double,
                                                        disambiguate: Boolean,
                                                        ntWrap: NonTerminalInstance[NT, R] => R
                                                       )(implicit sctx: SynthesisContext) {

  require(minLogProb < 0.0)

  import sctx.reporter._
  implicit protected val debugSection = leon.utils.DebugSectionSynthesis
  def verboseDebug(msg: => String) = {
    debug(msg)(leon.utils.DebugSectionSynthesisVerbose)
  }
  def ifVerboseDebug(body: (Any => Unit) => Any) = {
    ifDebug(NoPosition, body)(leon.utils.DebugSectionSynthesisVerbose)
  }

  val timers = sctx.timers.synthesis.applications.get("Prob-Enum")

  protected def productions(nt: NT): Seq[ProductionRule[NT, R]]

  protected def nthor(nt: NT): Double

  protected val coeff = sctx.findOptionOrDefault(SynthesisPhase.optProbwiseTopdownCoeff)

  type Sig = Seq[R]

  var generated = 0
  //var output = 0

  // Filter out seen expressions

  // A map from a signature of running on examples to an expansion that matches.
  // We consider expansions with equal signature identical
  protected val sigToNormalMemo = mutable.Map[(NT, Sig), Expansion[NT, R]]()
  // A map from an expansion to a representative that was found to be identical
  protected val normalizeMemo = mutable.Map[Expansion[NT, R], Expansion[NT, R]]()
  def expRedundant(e: Expansion[NT, R]) = normalizeMemo(e)

  // Disambiguate expressions by signature
  def sig(r: R): Option[Sig]

  // Returns normalized version of e, or None if it fails
  protected def normalize(e: Expansion[NT, R]): Option[Expansion[NT, R]] = {
    import leon.utils.CollectionUtils.MutableMapUtils
    e match {
      case NonTerminalInstance(_) =>
        // non-terminal instances are incomplete, thus not normalizable
        Some(e)
      case ProdRuleInstance(nt, rule, children) =>
        // If we have representative for this expression, return it
        normalizeMemo.orElseUpdate(e, {
          // Otherwise...
          // Lazily make a normalized version of this based on the normalized versions of its children
          lazy val fromNormalizedChildren = children.mapM(normalize).map(ProdRuleInstance(nt, rule, _))
          if (!e.complete) {
            // If e is not complete, we cannot compute signature,
            // so reconstructing from the normalized children is best we can do.
            fromNormalizedChildren
          } else {
            // If e is complete expression...

            // Calculate its signature (this may fail)
            sig(e.produce).flatMap { theSig =>
              // Look up in the signature map for an expansion with the same signature
              // If not found, fromNormalizedChildren will be the representative for this class.
              // Add it to the map and return it
              sigToNormalMemo.orElseUpdate( (e.nt, theSig), fromNormalizedChildren)
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
      val t1 = coeff * Math.log((score.nYes + 1.0) / (score.nExs + 1.0))
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

    var lastPrint: Int = 1

    def hasNext: Boolean = {
      try {
        prepareNext()
        worklist.nonEmpty
      } catch {
        case _: NoSuchElementException =>
          false
      }
    }

    def next: R = {
      EnumeratorStats.iteratorNextCallCount += 1
      prepareNext()
      assert(worklist.nonEmpty)
      val res = worklist.dequeue()
      ifDebug { printer =>
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
          val res = score.noExs.isEmpty
          if (res) {
            EnumeratorStats.partialEvalAcceptCount += 1
          } else {
            EnumeratorStats.partialEvalRejectionCount += 1
          }
          res
        }

        // Does elem have to be removed from the queue?
        // It is removed if it is either incomplete (i.e. needs further expansion), or fails some tests (i.e. needs to
        // be dropped).
        if (elem.logProb < minLogProb || !elem.expansion.complete || !compliesTests) {
          // If so, remove it
          worklist.dequeue()
          generated += 1
          ifDebug(printer =>
            if ((generated & (generated-1)) == 0) {
              printer(s"generated = $generated")
            }
          )
          verboseDebug(s"Dequeued (${elem.priority}): ${elem.expansion.falseProduce(ntWrap)}")

          if (elem.logProb >= minLogProb && compliesTests) {
            // If it is possible that the expansions of elem lead somewhere ...
            // First normalize it!
            // @mk: Dirty hack: This relies on the previous call to scorer.score for recursive calls
            val normalExpansionOpt = if (disambiguate) normalize(elem.expansion) else Some(elem.expansion)
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
                ifDebug { printer =>
                  if (worklist.size >= 2 * lastPrint) {
                    printer(s"Worklist size: ${worklist.size}")
                    printer(s"Accept / reject ratio: ${EnumeratorStats.partialEvalAcceptCount} /" +
                      s"${EnumeratorStats.partialEvalRejectionCount}")
                    lastPrint = worklist.size
                  }
                }
              case None =>
                debug(elem.expansion + " failed evaluation")
            }
          } else {
            // The element has failed partial evaluation ...
            ifVerboseDebug { printer =>
              val scoreTriple = (score.yesExs.size, score.noExs.size, score.maybeExs.size)
              printer(s"Element rejected. compliesTests = $compliesTests, scoreTriple = $scoreTriple.")
            }
          }
          // We dequeued an elemen, so we don't necessarily have an acceptable element
          // on the head of the queue. Call rec again.
          prepareNext()
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
          expansionPreNormal = normalizeMemo.getOrElse(expansion, expansion)
          // expansionPreNormal = expansion
        } yield {
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
              csHdExpPreNormal = normalizeMemo.getOrElse(csHdExp.expansion, csHdExp.expansion)
              // csHdExpPreNormal = csHdExp.expansion
            } yield {
              (csHdExpPreNormal :: csTl, csHdExp.logProb)
            }
        }

        for {
          (expansions, logProb) <- expandChildren(children)
          expPrime = ProdRuleInstance(nt, rule, expansions)
          expPrimePreNormal = normalizeMemo.getOrElse(expPrime, expPrime)
          // expPrimePreNormal = expPrime
        } yield {
          val logProbPrime = elem.logProb + logProb
          val horizonPrime = expPrimePreNormal.horizon(nthor)
          WorklistElement(expPrimePreNormal, logProbPrime, horizonPrime, elemScore, Some(elem))
        }
    }
  }
}
