package leon
package synthesis
package stoch

import java.time.LocalDateTime

import StatsUtils._
import Stats._
import purescala.Definitions._
import purescala.Expressions.Expr
import leon.utils.PreprocessingPhase
import leon.frontends.scalac.{ClassgenPhase, ExtractionPhase}
import leon.purescala.DefOps._

object Stats2Main {

  def main(args: Array[String]): Unit = {
    println(LocalDateTime.now())
    println(s"SELECT_FUNCTION_TYPES: ${StatsMain.SELECT_FUNCTION_TYPES}")
    println(s"SELECT_TUPLE_TYPES: ${StatsMain.SELECT_TUPLE_TYPES}")

    val frontend = ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false)

    val canaryFileName = args(0)
    val ctx = Main.processOptions(List(canaryFileName))
    val (_, modelProgram) = frontend.run(ctx, List(canaryFileName))

    val canaryModule = modelProgram.units.find(_.isMainUnit).get.modules.head

    val canaryTypes = getCanaryTypes(canaryModule)

    val modelClasses = modelProgram.definedClasses  .map(cl => fullName(cl)(modelProgram) -> cl).toMap
    val modelFuns    = modelProgram.definedFunctions.map(fd => fullName(fd)(modelProgram) -> fd).toMap

    val collectiveProgram = {

      val mainUnits = args.toSeq.tail.par.map { fileName =>
        val (_, program) = frontend.run(Main.processOptions(List(fileName)), List(fileName))

        val classMap = {
          program.definedClasses.map(cl => cl -> modelClasses.get(fullName(cl)(program))).toMap
        }

        val funMap = {
          program.definedFunctions.map(fd => fd -> modelFuns.get(fullName(fd)(program))).toMap
        }

        val strippedProgram = Program(program.units.filter(_.isMainUnit))

        val programNormalizer = definitionReplacer(funMap, classMap)

        val normalProgram = transformProgram(programNormalizer, strippedProgram)

        normalProgram.units
      }.seq.flatten

      val libUnits = modelProgram.units.filterNot(_.isMainUnit)

      //Program(libUnits ++ mainUnits)
      Program(mainUnits.toList)
    }

    //println("====== collective =======")
    //println(collectiveProgram)
    //println("====== \\collective =======")

    val allEs = allSubExprs2(collectiveProgram)
    //println("====== allSubExprs2 =======")
    //allEs foreach println
    //println("====== \\allSubExprs2 =======")

    val fase2 = canaryTypeFilter2(allEs, canaryTypes)
    //println("====== fase2 =======")
    //fase2 foreach println
    //println("====== \\fase2 =======")

    println("Printing canary types:")
    canaryTypes.foreach(println)

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

    val prodRules: UnitDef = PCFG2Emitter.emit2(modelProgram, canaryTypes, ecs2, fcs2, ls2)

    val prodRulesStr = replaceKnownNames(prodRules.toString)

    println("Printing production rules:")
    println(prodRulesStr)
  }

}
