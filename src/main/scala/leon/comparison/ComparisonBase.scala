package leon.comparison

import java.io.File

import leon.{LeonContext, Main}
import leon.frontends.scalac.ExtractionPhase
import leon.purescala.Definitions.{FunDef, Program}
import leon.utils.PreprocessingPhase


/**
  * Created by joachimmuth on 24.03.16.
  */
case class ComparisonBase(ctx: LeonContext, folder: String) {

  val listFunDef: List[FunDef] = extractListFunDef(recursiveListFilesInString(folder))

  def extractListFunDef(files: List[String]): List[FunDef] = {
    val extraction =  ExtractionPhase andThen new PreprocessingPhase(false)
    val (_, prog) = extraction.run(ctx, files)

    ComparisonPhase.getFunDef(ctx, prog)
  }

  def recursiveListFiles(f: File): List[File] = {
    val these = f.listFiles.toList
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }

  def recursiveListFilesInString(f: String): List[String] = {
    val file = new File(f)
    println("-----------")
    println("list files : ", recursiveListFiles(file))
    println("list files string : ", recursiveListFiles(file).map(f => f.getPath) )
    recursiveListFiles(file).map(f => f.getCanonicalPath)
  }

}
