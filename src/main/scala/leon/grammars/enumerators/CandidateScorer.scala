package leon
package grammars
package enumerators

import CandidateScorer.{MeetsSpec, Score}
import CandidateScorer.MeetsSpec.MeetsSpec
import synthesis.{Example, SynthesisContext}

import scala.collection.mutable.ArrayBuffer
import scala.util.control.Breaks

class CandidateScorer[NT, R](evalCandidate: (Expansion[NT, R], Example) => MeetsSpec,
                             getExs: Unit => Seq[Example]
                            )(implicit sctx: SynthesisContext) {

  val timers = sctx.timers.synthesis.applications.get("Prob-Enum")

  def score(expansion: Expansion[NT, R], skipExs: Set[Example], eagerReturnOnFalse: Boolean): Score = {
    timers.score.timed {
      if (eagerReturnOnFalse) {
        eagerReturnScore(expansion, skipExs)
      } else {
        fullScore(expansion, skipExs)
      }
    }
  }

  private def eagerReturnScore(expansion: Expansion[NT, R], skipExs: Set[Example]): Score = {
    val exs = getExs(())

    val yesExs = new ArrayBuffer[Example]()
    val noExs = new ArrayBuffer[Example]()
    val maybeExs = new ArrayBuffer[Example]()

    yesExs ++= skipExs
    val scoreBreaks = new Breaks
    scoreBreaks.breakable {
      for (ex <- exs if !skipExs.contains(ex)) {
        evalCandidate(expansion, ex) match {
          case MeetsSpec.YES => yesExs += ex
          case MeetsSpec.NO =>
            noExs += ex
            scoreBreaks.break
          case MeetsSpec.NOTYET => maybeExs += ex
        }
      }
    }

    Score(yesExs.toSet, noExs.toSet, maybeExs.toSet)
  }

  private def fullScore(expansion: Expansion[NT, R], skipExs: Set[Example]): Score = {
    val exs = getExs(())
    def classify(ex: Example) = if (skipExs.contains(ex)) MeetsSpec.YES else evalCandidate(expansion, ex)
    // val results = exs.par.groupBy(classify).mapValues(_.seq)
    val results = exs.groupBy(classify)
    Score(results.getOrElse(MeetsSpec.YES, Seq()).toSet,
      results.getOrElse(MeetsSpec.NO, Seq()).toSet,
      results.getOrElse(MeetsSpec.NOTYET, Seq()).toSet)
  }

}

object CandidateScorer {

  case class Score(yesExs: Set[Example], noExs: Set[Example], maybeExs: Set[Example]) {
    val nYes: Int = yesExs.size
    val nExs: Int = yesExs.size + noExs.size + maybeExs.size
  }

  object MeetsSpec extends Enumeration {
    type MeetsSpec = Value
    val YES, NO, NOTYET = Value
  }

}
