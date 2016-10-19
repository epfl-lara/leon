package leon
package synthesis.stoch

import scala.util.Random

import Statistics.ExprConstrStats
import Statistics.addStats
import Statistics.exprConstrStatsToString
import Statistics.getExprConstrStats
import leon.Main
import leon.Pipeline
import leon.purescala.Types.TypeTree
import leon.grammars.ProductionRule
import leon.grammars.BaseGrammar
import leon.purescala.Expressions.Expr
import leon.purescala.Types.BooleanType
import leon.grammars.Expansion

object StatisticsExtractorMain {

  def main(args: Array[String]): Unit = {
    mainPCFGExpansionStream(args)
    // mainExtractGrammar(args)
  }

  def mainPCFGExpansionStream(args: Array[String]): Unit = {
    val ctx = Main.processOptions(List())

    type LabelType = TypeTree
    val grammar: LabelType => Seq[ProductionRule[LabelType, Expr]] =
      typeTree => BaseGrammar.computeProductions(typeTree)(ctx)
    val expansionIterator = Expansion.expansionIterator(BooleanType, grammar)

    var maxProdSize = 0
    for (i <- 1 to 1000000) {
      val next = expansionIterator.next
      assert(next ne null)
      // println(s"${next._1}: ${next._2}")

      if (next._1.size > maxProdSize /* || i % 100 == 0 */ ) {
        println(s"${i}: (Size: ${next._1.size}, Expr: ${next._1.produce}, Probability: ${next._2})")
        maxProdSize = next._1.size
      }
    }
  }

  def mainExtractGrammar(args: Array[String]): Unit = {
    var globalStatsTrain: ExprConstrStats = Map()
    var globalStatsTest: ExprConstrStats = Map()
    val random = new Random()

    args.par.foreach(fileName => {
      val fileStats = procFile(fileName)
      if (random.nextDouble() <= 0.9) {
        this.synchronized {
          globalStatsTrain = addStats(globalStatsTrain, fileStats)
        }
      } else {
        this.synchronized {
          globalStatsTest = addStats(globalStatsTest, fileStats)
        }
      }
    })

    println("Printing training data:")
    println(exprConstrStatsToString(globalStatsTrain))
    println("Printing test data:")
    println(exprConstrStatsToString(globalStatsTest))
    println("Computing score:")
    val score = dist(globalStatsTrain, globalStatsTest)
    println(s"Score: ${score}")
  }

  def procFile(fileName: String): ExprConstrStats = {
    val args = List("--pcfg-stats", fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  def pipeline: Pipeline[List[String], ExprConstrStats] = {
    import frontends.scalac.ClassgenPhase
    import frontends.scalac.ExtractionPhase
    ClassgenPhase andThen ExtractionPhase andThen SimpleFunctionApplicatorPhase(getExprConstrStats)
  }

  def dist(statsTrain: ExprConstrStats, statsTest: ExprConstrStats): (Double, Double) = {
    val numTestExprs = statsTest.mapValues(_.values.sum).values.sum
    println(s"numTestExprs: ${numTestExprs}")

    var numCorrectTestExprs = 0.0
    var numRandomCorrectTestExprs = 0.0
    for (typeTree <- statsTest.toList.sortBy(-_._2.values.sum).map(_._1)) {
      val typeFreqTest = statsTest(typeTree).values.sum
      val numConstrs = statsTest(typeTree).values.size
      println(s"Considering type ${typeTree}, which occurs ${typeFreqTest} times in test, and with ${numConstrs} constructors")

      val predConstrOpt = statsTrain.getOrElse(typeTree, Map()).toList.sortBy(-_._2).headOption
      predConstrOpt match {
        case Some((constr, _)) => {
          val thisTypeCorrect = statsTest(typeTree).getOrElse(constr, 0)
          println(s"  Train suggests constructor ${constr} which was used ${thisTypeCorrect} times in test")
          numCorrectTestExprs = numCorrectTestExprs + thisTypeCorrect
        } case None => {
          numCorrectTestExprs = numCorrectTestExprs + (typeFreqTest.asInstanceOf[Double] / numConstrs)
        }
      }

      numRandomCorrectTestExprs = numRandomCorrectTestExprs + (typeFreqTest.asInstanceOf[Double] / numConstrs)
    }

    val ourScore = numCorrectTestExprs / numTestExprs
    val randomScore = numRandomCorrectTestExprs / numTestExprs
    (ourScore, randomScore)
  }

}