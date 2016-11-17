package leon
package grammars
package enumerators

import CandidateScorer.{Score, MeetsSpec}
import CandidateScorer.MeetsSpec.MeetsSpec
import synthesis.Example

import scala.collection.mutable.ArrayBuffer
import scala.util.control.Breaks

class CandidateScorer[R](
  evalCandidate: (Expansion[_, R], Example) => MeetsSpec,
  getExs: Unit => Seq[Example]
)(implicit ctx: LeonContext) {

  def score(expansion: Expansion[_, R], skipExs: Set[Example], eagerReturnOnFalse: Boolean): Score = {
    ctx.timers.eval.start()
    val ans = if (eagerReturnOnFalse) {
      val yesExs = new ArrayBuffer[Example]()
      val noExs = new ArrayBuffer[Example]()
      val maybeExs = new ArrayBuffer[Example]()

      yesExs ++= skipExs
      val scoreBreaks = new Breaks
      scoreBreaks.breakable {
        for (ex <- getExs(()) if !skipExs.contains(ex)) {
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
    } else {
      def classify(ex: Example) = if (skipExs.contains(ex)) MeetsSpec.YES else evalCandidate(expansion, ex)
      val results = getExs(()).par.groupBy(classify).mapValues(_.seq)
      Score(results.getOrElse(MeetsSpec.YES, Seq()).toSet,
        results.getOrElse(MeetsSpec.NO, Seq()).toSet,
        results.getOrElse(MeetsSpec.NOTYET, Seq()).toSet)
    }
    ctx.timers.eval.stop()
    ans
  }

}

object CandidateScorer {

  case class Score(yesExs: Set[Example], noExs: Set[Example], maybeExs: Set[Example]) {
    def nYes: Int = yesExs.size
    def nExs: Int = yesExs.size + noExs.size + maybeExs.size
  }

  val SEED_SCORE: Score = Score(Set(), Set(), Set())

  object MeetsSpec extends Enumeration {
    type MeetsSpec = Value
    val YES, NO, NOTYET = Value
  }

}
