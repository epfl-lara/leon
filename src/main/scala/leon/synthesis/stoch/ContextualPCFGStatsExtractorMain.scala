package leon
package synthesis
package stoch

import ContextualPCFGStats._
import leon.utils.PreprocessingPhase

import scala.util.Random

object ContextualPCFGStatsExtractorMain {

  def main(args: Array[String]): Unit = {
    @volatile var globalStatsTrain: AncStats = Map()
    @volatile var globalStatsTest: AncStats = Map()
    val random = new Random(0) // Remove this 0 to make non-deterministic

    val fileStats = args.tail.par.map(fileName => fileName -> procFile(fileName)).toMap
    for (fileName <- args.tail) {
      if (random.nextDouble() <= 0.9) {
        globalStatsTrain = addStats(globalStatsTrain, fileStats(fileName))
      } else {
        globalStatsTest = addStats(globalStatsTest, fileStats(fileName))
      }
    }

    globalStatsTrain = reduceContextDepth(globalStatsTrain, 2)
    globalStatsTest = reduceContextDepth(globalStatsTest, 2)

    println("Printing training data:")
    println(ancStatsToString(globalStatsTrain))
    println("Printing test data:")
    println(ancStatsToString(globalStatsTest))
    /* println("Computing score:")
    val score = dist(globalStatsTrain, globalStatsTest)
    println(s"Score: $score") */
  }

  def procFile(fileName: String): AncStats = {
    val args = List(fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  def pipeline: Pipeline[List[String], AncStats] = {
    import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
    ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false) andThen
      SimpleFunctionApplicatorPhase(getAncStats)
  }

  /* def dist(statsTrain: AncStats, statsTest: AncStats): (Double, Double) = {
    val numTestExprs = statsTest.mapValues(_.values.sum).values.sum
    println(s"numTestExprs: $numTestExprs")

    var numCorrectTestExprs = 0.0
    var numRandomCorrectTestExprs = 0.0
    for (typeTree <- statsTest.toList.sortBy(-_._2.values.sum).map(_._1)) {
      val typeFreqTest = statsTest(typeTree).values.sum
      val numConstrs = statsTest(typeTree).values.size
      println(s"Considering type $typeTree, which occurs $typeFreqTest times in test, and with $numConstrs constructors")

      val predConstrOpt = statsTrain.getOrElse(typeTree, Map()).toList.sortBy(-_._2).headOption
      predConstrOpt match {
        case Some((constr, _)) =>
          val thisTypeCorrect = statsTest(typeTree).getOrElse(constr, 0)
          println(s"  Train suggests constructor $constr which was used $thisTypeCorrect times in test")
          numCorrectTestExprs = numCorrectTestExprs + thisTypeCorrect
        case None =>
          numCorrectTestExprs = numCorrectTestExprs + (typeFreqTest.asInstanceOf[Double] / numConstrs)
      }

      numRandomCorrectTestExprs = numRandomCorrectTestExprs + (typeFreqTest.asInstanceOf[Double] / numConstrs)
    }

    val ourScore = numCorrectTestExprs / numTestExprs
    val randomScore = numRandomCorrectTestExprs / numTestExprs
    (ourScore, randomScore)
  } */

}