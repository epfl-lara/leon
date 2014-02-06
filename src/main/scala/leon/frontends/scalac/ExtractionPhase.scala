/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package frontends.scalac

import purescala.Definitions.Program
import purescala.Common.FreshIdentifier

import utils._

import scala.tools.nsc.{Settings=>NSCSettings,CompilerCommand}

object ExtractionPhase extends LeonPhase[List[String], Program] {

  val name = "Scalc Extraction"
  val description = "Extraction of trees from the Scala Compiler"

  implicit val debug = DebugSectionTrees

  def run(ctx: LeonContext)(args: List[String]): Program = {

    val settings = new NSCSettings

    settings.classpath.value = ctx.settings.classPath.mkString(":")
    settings.skip.value      = List("patmat")

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

      (compiler.leonExtraction.units, compiler.leonExtraction.modules) match {
        case (Nil, Nil) =>
          ctx.reporter.fatalError("Error while compiling. Empty input?")

        case (_, Nil) =>
          ctx.reporter.fatalError("Error while compiling.")

        case (_, modules) =>
          if (ctx.reporter.errorCount > 0 && ctx.settings.strictCompilation) {
            ctx.reporter.fatalError("Error while compiling.")
          } else {
            val pgm = Program(FreshIdentifier("<program>"), modules)
            ctx.reporter.debug(pgm.asString(ctx))
            pgm
          }
      }
    } else {
      ctx.reporter.fatalError("No input program.")
    }
  }
}
