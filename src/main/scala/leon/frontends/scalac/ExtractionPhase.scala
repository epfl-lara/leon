/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package frontends.scalac

import purescala.Definitions.Program

import scala.tools.nsc.{Settings=>NSCSettings,CompilerCommand}

object ExtractionPhase extends LeonPhase[List[String], Program] {

  val name = "Scalc Extraction"
  val description = "Extraction of trees from the Scala Compiler"

  def run(ctx: LeonContext)(args: List[String]): Program = {

    val settings = new NSCSettings

    settings.classpath.value = ctx.settings.classPath.mkString(":")
    settings.skip.value      = List("patmat")
//    settings.log.value       = List("all")

    val compilerOpts = args.filterNot(_.startsWith("--"))

    val command = new CompilerCommand(compilerOpts, settings) {
      override val cmdName = "leon"
    }

    if(command.ok) {
      // Debugging code for classpath crap
      // new scala.tools.util.PathResolver(settings).Calculated.basis.foreach { cp =>
      //   cp.foreach( p =>
      //     println(" => "+p.toString)
      //   )
      // }

      val compiler = new ScalaCompiler(settings, ctx)
      val run = new compiler.Run
      run.compile(command.files)

      compiler.leonExtraction.program match {
        case Some(p) =>
          if (ctx.reporter.errorCount > 0 && ctx.settings.strictCompilation) {
            ctx.reporter.fatalError("Error while compiling.")
          } else {
            p
          }
        case None =>
          ctx.reporter.fatalError("Error while compiling.")
      }
    } else {
      ctx.reporter.fatalError("No input program.")
    }
  }
}
