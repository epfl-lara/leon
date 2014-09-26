/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package frontends.scalac

import purescala.Definitions.Program
import purescala.Common.FreshIdentifier

import utils._

import scala.tools.nsc.{Settings=>NSCSettings,CompilerCommand}

object ExtractionPhase extends LeonPhase[List[String], Program] {

  val name = "Scalac Extraction"
  val description = "Extraction of trees from the Scala Compiler"

  implicit val debug = DebugSectionTrees

  def run(ctx: LeonContext)(args: List[String]): Program = {
    val timer = ctx.timers.frontend.start()

    val settings = new NSCSettings

    val neededClasses = List[Class[_]](
      scala.Predef.getClass
    )

    val urls = neededClasses.map{ _.getProtectionDomain().getCodeSource().getLocation() }

    val classpath = urls.map(_.getPath).mkString(":")

    settings.classpath.value = classpath
    settings.usejavacp.value = false
    settings.Yrangepos.value = true
    settings.skip.value      = List("patmat")

    val libFiles = Build.libFiles
    
    val injected = if (ctx.settings.injectLibrary) {
      libFiles
    } else {
      libFiles.filter(f => (f.contains("/lang/") && !f.contains("/lang/string/")) || f.contains("/annotation/"))
    }

    val compilerOpts = injected ::: args.filterNot(_.startsWith("--"))

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

      timer.stop()

      compiler.leonExtraction.setImports(compiler.saveImports.imports )

      val pgm = Program(FreshIdentifier("__program"), compiler.leonExtraction.compiledUnits)
      pgm
    } else {
      ctx.reporter.fatalError("No input program.")
    }
  }
}
