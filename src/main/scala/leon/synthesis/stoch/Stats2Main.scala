package leon
package synthesis
package stoch

import StatsUtils._
import leon.purescala.Definitions.FunDef
import leon.purescala.Expressions.{Expr, Variable}
import leon.synthesis.stoch.Stats._
import leon.utils.PreprocessingPhase

object Stats2Main {

  val SELECT_FUNCTION_TYPES: Boolean = false
  val SELECT_TUPLE_TYPES: Boolean = false

  def main(args: Array[String]): Unit = {
    val canaryFileName = args(1)
    val canaryExprs = StatsMain.procFiles(canaryFileName)
    val canaryTypes = canaryExprs.filter(_.isInstanceOf[Variable])
                                 .map(_.asInstanceOf[Variable])
                                 .filter(_.id.name.contains("f82c414"))
                                 .map(v => v.id.name -> v.getType).toMap
    println("Printing canary types:")
    canaryTypes.foreach(println)

    val fase = args.drop(2).toSeq.par
                   .map(fname => fname -> canaryTypeFilter2(procFiles2(fname, canaryFileName)))
                   .filter(_._2.nonEmpty)
                   .toMap.seq

    /* for ((fname, exprs) <- fase) {
      println(s"Printing interesting expressions from ${fname}")
      for (expr <- exprs) {
        println(s"$fname, ${expr.getType}, ${expr.getType.getClass}, ${expr.getClass}")
      }
    } */

    val allTypeParams = fase.values.flatten.map(_._1).map(exprConstrFuncType).flatMap(getTypeParams).toSeq.distinct
    val ecs: ECS2 = fase.values.map(exprs => groupExprs2(allTypeParams, canaryTypes, exprs))
                               .fold(Map())(ecs2Add)
                               .mapValues(_.mapValues(_.mapValues(_.mapValues(_.filterNot(isCanaryExpr)))))
                               .mapValues(_.mapValues(_.mapValues(_.filterKeys(_.forall(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams))))))
                               .filterKeys(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams))

    println("Printing coarse ECS2:")
    println(Stats.ecs2ToStringCoarse(ecs))

    println("Printing ECS2:")
    println(Stats.ecs2ToString(ecs))

    val fcs: FCS2 = getFCS2(ecs)
    println("Printing FCS2:")
    println(Stats.fcs2ToString(fcs))

    val ls: LS2 = getLS2(ecs)
    println("Printing LS2:")
    println(Stats.ls2ToString(ls))

    /* val prodRules: Seq[FunDef] = PCFGEmitter.emit(canaryExprs, canaryTypes, ecs, fcs, ls)
    println("Printing production rules:")
    for (rule <- prodRules) {
      println(rule)
      println()
    } */
  }

  def procFiles2(fileNames: String*): Seq[(Expr, Option[(Int, Expr)])] = {
    val ctx = Main.processOptions(fileNames.toSeq)
    try {
      pipeline2.run(ctx, fileNames.toList)._2
    } catch {
      case ex: Exception =>
        println(s"procFiles($fileNames): Encountered exception $ex")
        Seq()
    }
  }

  def pipeline2: Pipeline[List[String], Seq[(Expr, Option[(Int, Expr)])]] = {
    import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
    ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false) andThen
      SimpleFunctionApplicatorPhase(allSubExprs2)
  }

}
