package leon
package synthesis
package stoch

import PCFGStats._
import leon.purescala.Expressions.{Expr, FunctionInvocation, Literal}
import leon.synthesis.stoch.Stats.{ExprConstrStats, FunctionCallStats, LitStats}
import leon.utils.PreprocessingPhase

object StatsMain {

  def main(args: Array[String]): Unit = {
    val ase = args.tail.toSeq.par.flatMap(procFile).seq

    val allTypeParams = ase.map(_.getType).flatMap(getTypeParams).distinct
    val tase = ase.groupBy(expr => normalizeType(allTypeParams, expr.getType))
    val ecs: ExprConstrStats = tase.mapValues(_.groupBy(_.getClass))
    println("Printing expression constructor stats:")
    println(Stats.ecsToString(ecs))

    val allFuncInvokes = ase.filter(_.isInstanceOf[FunctionInvocation])
                            .map(_.asInstanceOf[FunctionInvocation])
    val tafi = allFuncInvokes.groupBy(fi => normalizeType(allTypeParams, fi.getType))
    val fcs: FunctionCallStats = tafi.mapValues(_.groupBy(_.tfd))
    println("Printing function call stats:")
    println(Stats.fcsToString(fcs))

    val ls: LitStats = tase.mapValues(_.filter(_.isInstanceOf[Literal[_]])
                                       .map(_.asInstanceOf[Literal[_]])
                                       .groupBy(_.value))
    println("Printing literal occurrence statistics:")
    println(Stats.lsToString(ls))
  }

  def procFile(fileName: String): Seq[Expr] = {
    val args = List(fileName)
    val ctx = Main.processOptions(args)
    pipeline.run(ctx, args)._2
  }

  // def pipeline: Pipeline[List[String], ExprConstrStats] = {
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
