package leon
package synthesis
package stoch

import java.time.LocalDateTime

import StatsUtils._
import leon.purescala.Definitions.UnitDef
import leon.purescala.Expressions.{Expr, Variable}
import leon.synthesis.stoch.Stats._
import leon.utils.PreprocessingPhase

object Stats2Main {

  def main(args: Array[String]): Unit = {
    println(LocalDateTime.now())
    println(s"SELECT_FUNCTION_TYPES: ${StatsMain.SELECT_FUNCTION_TYPES}")
    println(s"SELECT_TUPLE_TYPES: ${StatsMain.SELECT_TUPLE_TYPES}")

    val canaryFileName = args(1)
    val canaryExprs = StatsMain.procFiles(canaryFileName)
    val canaryTypes = canaryExprs.filter(_.isInstanceOf[Variable])
                                 .map(_.asInstanceOf[Variable])
                                 .filter(_.id.name.contains("f82c414"))
                                 .map(v => v.id.name -> v.getType).toMap
    println("Printing canary types:")
    canaryTypes.foreach(println)

    val fase2 = args.drop(2).toSeq.par
                   .map(fname => fname -> canaryTypeFilter2(procFiles2(fname, canaryFileName)))
                   .filter(_._2.nonEmpty)
                   .toMap.seq
    val fase1 = fase2.mapValues(_.map(_._1))

    /* for ((fname, epar) <- fase2) {
      println(s"Printing interesting expressions from $fname")
      for ((expr, par) <- epar) {
        println(s"$fname, $expr, ${expr.getType}, ${expr.getType.getClass}, ${expr.getClass}")
      }
    } */

    val allTypeParams = fase2.values.flatten.map(_._1).map(exprConstrFuncType).flatMap(getTypeParams).toSeq.distinct
    val ecs2: ECS2 =
      fase2.map { case (fileName, exprs) => groupExprs2(fileName, allTypeParams, canaryTypes, exprs) }
           .fold(Map())(ecs2Add)
           .mapValues(_.mapValues(_.mapValues(_.mapValues(_.filterNot(isCanaryExpr)))))
           .mapValues(_.mapValues(_.mapValues(_.filterKeys(_.forall(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams))))))
           .filterKeys(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams))
    val ecs1: ExprConstrStats =
      fase1.map { case (fileName, exprs) => groupExprs(fileName, allTypeParams, canaryTypes, exprs) }
           .fold(Map())(ecsAdd)
           .mapValues(_.mapValues(_.mapValues(_.filterNot(isCanaryExpr))))
           .mapValues(_.mapValues(_.filterKeys(_.forall(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams)))))
           .filterKeys(tt => isSelectableTypeStrict(tt, canaryTypes.values.toSeq, allTypeParams))

    println("Printing coarse ECS2:")
    println(Stats.ecs2ToStringCoarse(ecs2))

    println("Printing ECS2:")
    println(Stats.ecs2ToString(ecs2))

    val fcs2: FCS2 = getFCS2(ecs2)
    println("Printing FCS2:")
    println(Stats.fcs2ToString(fcs2))
    val fcs1: FunctionCallStats = getFunctionCallStats(ecs1)

    val ls2: LS2 = getLS2(ecs2)
    println("Printing LS2:")
    println(Stats.ls2ToString(ls2))
    val ls1: LitStats = getLitStats(ecs1)

    val prodRules: UnitDef = PCFG2Emitter.emit2(canaryExprs, canaryTypes, ecs1, fcs1, ls1, ecs2, fcs2, ls2)
    val prodRulesStr = prodRules.toString
                                .replaceAll("variable\\$\\d*\\[", "variable[")
                                .replaceAll("List\\$\\d*\\[", "List[")
                                .replaceAll("Option\\$\\d*\\[", "Option[")
                                .replaceAll("case class (.*)\\(", "implicit class $1(val ")
    println("Printing production rules:")
    println(prodRulesStr)
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
