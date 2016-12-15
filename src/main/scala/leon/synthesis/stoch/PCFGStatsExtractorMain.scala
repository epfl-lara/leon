package leon
package synthesis
package stoch

import PCFGStats.{ExprConstrStats, addStats, exprConstrStatsToString, getExprConstrStats}
import leon.purescala.Expressions._
import leon.purescala.Types.BooleanType
import leon.utils.PreprocessingPhase

import scala.util.Random

object PCFGStatsExtractorMain {

  def main(args: Array[String]): Unit = {
    @volatile var globalStatsTrain: ExprConstrStats = Map()
    @volatile var globalStatsTest: ExprConstrStats = Map()
    val random = new Random(0) // Remove this 0 to make non-deterministic

    val fileStats = args.tail.par.map(fileName => fileName -> procFile(fileName)).toMap
    for (fileName <- args.tail) {
      if (random.nextDouble() <= 0.9) {
        globalStatsTrain = addStats(globalStatsTrain, fileStats(fileName))
      } else {
        globalStatsTest = addStats(globalStatsTest, fileStats(fileName))
      }
    }

    // PCFGEmitter.emit(Set(), globalStatsTrain).foreach(println)
    /* println(PCFGEmitter.emit(Set(), BooleanType, classOf[And], globalStatsTrain))
    println(PCFGEmitter.emit(Set(), BooleanType, classOf[Or], globalStatsTrain))
    println(PCFGEmitter.emit(Set(), BooleanType, classOf[Not], globalStatsTrain))
    println(PCFGEmitter.emit(Set(), BooleanType, classOf[Equals], globalStatsTrain))
    println(PCFGEmitter.emit(Set(), BooleanType, classOf[Plus], globalStatsTrain)) */

    println("Printing training data:")
    println(exprConstrStatsToString(globalStatsTrain))
    println("Printing test data:")
    println(exprConstrStatsToString(globalStatsTest))
    println("Computing score:")
    val score = dist(globalStatsTrain, globalStatsTest)
    println(s"Score: $score")
  }

  def procFile(fileName: String): ExprConstrStats = {
    val args = List(fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  def pipeline: Pipeline[List[String], ExprConstrStats] = {
    import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
    ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false) andThen
      SimpleFunctionApplicatorPhase(getExprConstrStats)
  }

  def dist(statsTrain: ExprConstrStats, statsTest: ExprConstrStats): (Double, Double) = {
    val statsTrainC = statsTrain.mapValues(_.mapValues(_.size))
    val statsTestC = statsTest.mapValues(_.mapValues(_.size))

    val numTestExprs = statsTestC.mapValues(_.values.sum).values.sum
    println(s"numTestExprs: $numTestExprs")

    var numCorrectTestExprs = 0.0
    var numRandomCorrectTestExprs = 0.0
    for (typeTree <- statsTestC.toSeq.sortBy(-_._2.values.sum).map(_._1)) {
      val typeFreqTest = statsTestC(typeTree).values.sum
      val numConstrs = statsTestC(typeTree).values.size
      println(s"Considering type $typeTree, which occurs $typeFreqTest times in test, and with $numConstrs constructors")

      val predConstrOpt = statsTrainC.getOrElse(typeTree, Map()).toList.sortBy(-_._2).headOption
      predConstrOpt match {
        case Some((constr, _)) =>
          val thisTypeCorrect = statsTestC(typeTree).getOrElse(constr, 0)
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
  }

}