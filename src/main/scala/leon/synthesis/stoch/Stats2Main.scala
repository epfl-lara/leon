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
  import java.io._
  def main(args: Array[String]): Unit = {
    println(LocalDateTime.now())
    println(s"SELECT_FUNCTION_TYPES: ${StatsMain.SELECT_FUNCTION_TYPES}")
    println(s"SELECT_TUPLE_TYPES: ${StatsMain.SELECT_TUPLE_TYPES}")

    val frontend = ClassgenPhase andThen
      ExtractionPhase andThen
      new PreprocessingPhase(false)

    val cnt = new leon.utils.UniqueCounter[Unit]

    new File("tmp-corpus").mkdir()

    def processFile(fileName: String) = {
      val content = scala.io.Source.fromFile(fileName).getLines.mkString("\n")
      val c = cnt.nextGlobal
      new File("tmp-corpus/test$" + c).mkdir()
      val toFileName = "tmp-corpus/test$" + c + new File(fileName).getName
      val toFile = new File(toFileName)
      toFile.createNewFile()
      val pw = new PrintWriter(toFile)
      pw.write("package test$" + c + "\n" + content)
      pw.close()
      toFileName
    }

    val corpus = args.toSeq.drop(2).map(processFile).toList
    val canaryFileName = args(1)

    val (_, bigProgram) = frontend.run(Main.processOptions(corpus :+ canaryFileName), corpus :+ canaryFileName)

    val canaryModule = bigProgram.units.find(u => args(1).contains(u.id.name)).get.modules.head

    val canaryTypes = getCanaryTypes(canaryModule)

    val allEs = allSubExprs2(bigProgram)
    //val allEs = allSubExprs2(Program(bigProgram.units.filter(_.isMainUnit)))

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

    val prodRules1 = PCFGEmitter.emit(bigProgram, ecs1, fcs1, ls1)
    println("Printing production rules 1")
    println(replaceKnownNames(prodRules1.toString))

    val prodRules2: UnitDef = PCFG2Emitter.emit2(bigProgram, canaryTypes, ecs2, fcs2, ls2)
    println("Printing production rules:")
    println(replaceKnownNames(prodRules2.toString))
  }

}
