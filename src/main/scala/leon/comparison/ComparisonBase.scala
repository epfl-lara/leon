package leon.comparison

import leon.{LeonContext, Main}
import leon.frontends.scalac.ExtractionPhase
import leon.purescala.Definitions.{FunDef, Program}


/**
  * Created by joachimmuth on 24.03.16.
  */
case class ComparisonBase(files: List[String]) {

  val listFunDef: List[FunDef] = extractListFunDef(files)

  def extractListFunDef(files: List[String]): List[FunDef] = {
    val extraction = ExtractionPhase
    val ctx: LeonContext = createLeonContext()

    val (_, prog) = extraction.run(ctx, files)

    val ret = ComparisonPhase.getFunDef(ctx, prog)
    println("try to understand what happen in comparisonBase")
    println("file", files.toString())
    println("listFunDef ", ret)

    ret
  }


  def createLeonContext(): LeonContext =
    Main.processOptions(Seq("testcases/synthesis/BinaryTree.scala"))

}
