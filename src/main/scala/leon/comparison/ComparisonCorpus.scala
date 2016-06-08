package leon.comparison

import java.io.File
import java.nio.file.{Paths, Files}

import leon.LeonContext
import leon.frontends.scalac.ExtractionPhase
import leon.purescala.Definitions.{FunDef, Program}
import leon.utils.PreprocessingPhase


/**
  * Created by joachimmuth on 24.03.16.
  *
  * Extract list of all FunDef existing in the objects of the targeted folder.
  * Typically the folder is "comparison-base" (chosen in ComparisonPhase).
  */
case class ComparisonCorpus(ctx: LeonContext, folder: String) {

  val program: Program = extraction(recursiveListFilesInString(folder))
  val funDefs: List[FunDef] = extractFunDefs()

  def extraction(files: List[String]): _root_.leon.purescala.Definitions.Program = {
    val extraction =  ExtractionPhase andThen new PreprocessingPhase(false)
    val (_, prog) = extraction.run(ctx, files)
    prog
  }

  def extractFunDefs(): List[FunDef] = ComparisonPhase.getFunDef(ctx, program)


  def recursiveListFiles(f: File): List[File] = {
    val these = f.listFiles.toList
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }

  def recursiveListFilesInString(f: String): List[String] = {
    if(! Files.exists(Paths.get(f))) {
      ctx.reporter.error("Path of corpus folder doesn't exist: " + f)
      ctx.reporter.error("Program aborted")
      java.lang.System.exit(0)
    }
    val file = new File(f)
    recursiveListFiles(file).map(f => f.getCanonicalPath)
  }

}
