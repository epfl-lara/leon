package leon
package synthesis
package stoch

import java.time.LocalDateTime

import StatsUtils._
import Stats._
import purescala.Definitions.UnitDef
import purescala.Expressions.{Expr, Variable}
import leon.utils.PreprocessingPhase

object Stats2Main {

  def main(args: Array[String]): Unit = {
    println(LocalDateTime.now())
    println(s"SELECT_FUNCTION_TYPES: ${StatsMain.SELECT_FUNCTION_TYPES}")
    println(s"SELECT_TUPLE_TYPES: ${StatsMain.SELECT_TUPLE_TYPES}")

    val canaryFileName = args(1)
    val canaryExprs = StatsMain.procFiles(canaryFileName)
    val canaryTypes = canaryExprs.collect {
      case v: Variable if v.id.name.contains("f82c414") =>
        v.id.name -> v.getType
    }.toMap
    println("Printing canary types:")
    canaryTypes.foreach(println)

    val fase2 = args.drop(2).toSeq.par
                   .map(f => canaryTypeFilter2(procFiles2(f, canaryFileName)))
                   .filter(_.nonEmpty)
                   .seq.flatten
    val fase1 = fase2.map(_._1)

    val ecs2: ECS2 = groupAndFilterExprs2(canaryTypes, fase2)
    val ecs1: ExprConstrStats = groupAndFilterExprs(canaryTypes, fase1)
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

    val prodRulesStr = replaceKnownNames(prodRules.toString)

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
