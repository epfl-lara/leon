package leon
package synthesis
package stoch

import StatsUtils._
import leon.purescala.Definitions.FunDef
import leon.purescala.Expressions.{Expr, Variable}
import leon.purescala.Types.TypeTree
import leon.synthesis.stoch.Stats.{ExprConstrStats, FunctionCallStats, LitStats, ecsAdd}
import leon.utils.PreprocessingPhase

object StatsMain {

  def main(args: Array[String]): Unit = {
    val canaryFileName = args(1)
    val canaryExprs = procFiles(canaryFileName)
    val canaryTypes = canaryExprs.filter(_.isInstanceOf[Variable])
                                 .map(_.asInstanceOf[Variable])
                                 .filter(_.id.name.contains("f82c414"))
                                 .map(v => v.id.name -> v.getType).toMap
    println("Printing canary types:")
    canaryTypes.foreach(println)

    val fase = args.drop(2).toSeq.par
                   .map(fname => fname -> canaryTypeFilter(procFiles(fname, canaryFileName)))
                   .toMap.seq

    /* for ((fname, exprs) <- fase) {
      println(s"Printing interesting expressions from ${fname}")
      for (expr <- exprs) {
        println(s"$fname, ${expr.getType}, ${expr.getType.getClass}, ${expr.getClass}")
      }
    } */

    val allTypeParams = fase.values.flatten.map(exprConstrFuncType).flatMap(getTypeParams).toSeq.distinct
    val ecs: ExprConstrStats = fase.values.map(exprs => groupExprs(allTypeParams, canaryTypes, exprs))
                                          .fold(Map())(ecsAdd)
                                          .mapValues(_.mapValues(_.mapValues(_.filterNot(isCanaryExpr))))

    println("Printing coarse expression constructor stats:")
    println(Stats.ecsToStringCoarse(ecs))

    println("Printing expression constructor stats:")
    println(Stats.ecsToString(ecs))

    val fcs: FunctionCallStats = getFunctionCallStats(ecs)
    println("Printing function call stats:")
    println(Stats.fcsToString(fcs))

    val ls: LitStats = getLitStats(ecs)
    println("Printing literal occurrence statistics:")
    println(Stats.lsToString(ls))

    val productions: Seq[FunDef] = PCFGEmitter.emit(canaryExprs, canaryTypes, ecs, fcs, ls)
    println("Printing production rules:")
    productions.foreach(println)
  }

  def procFiles(fileNames: String*): Seq[Expr] = {
    val ctx = Main.processOptions(fileNames.toSeq)
    pipeline.run(ctx, fileNames.toList)._2
  }

  def pipeline: Pipeline[List[String], Seq[Expr]] = {
    import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
    ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false) andThen
      SimpleFunctionApplicatorPhase(allSubExprs)
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
