/* Copyright 2009-2016 EPFL, Lausanne */

package leon.solvers.isabelle

import java.io.FileWriter
import java.nio.file.{Files, Paths}

import scala.concurrent._
import scala.concurrent.duration._

import leon.LeonContext
import leon.OptionsHelpers._
import leon.GlobalOptions
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Common._
import leon.solvers._
import leon.utils._

import info.hupel.isabelle.{Program => _, _}
import info.hupel.isabelle.api._
import info.hupel.isabelle.setup._

import monix.execution.Scheduler.Implicits.global

object IsabelleEnvironment {

  private implicit val debugSection = DebugSectionIsabelle

  def apply(context: LeonContext, program: Program): Future[IsabelleEnvironment] = {
    LeonLoggerFactory.reporter = context.reporter

    val version = Version(isabelleVersion)
    val dump = context.findOptionOrDefault(Component.optDump)
    val strict = context.findOptionOrDefault(Component.optStrict)

    val funFilter =
      // FIXME duplicated from AnalysisPhase
      filterInclusive[FunDef](context.findOption(GlobalOptions.optFunctions).map(fdMatcher(program)), Some(_.annotations contains "library"))

    val funs = program.definedFunctions.filter(funFilter)

    val scripts = funs.flatMap { fun =>
      val name = fun.qualifiedName(program)
      fun.extAnnotations.get("isabelle.script") match {
        case Some(List(Some(name: String), Some(source: String))) => Some(name -> source)
        case Some(List(_, _)) =>
          context.reporter.fatalError(s"In script for function definition $name: expected a string literal as name and a string literal as source")
        case Some(_) =>
          context.reporter.internalError(s"Script for function definition $name")
        case None =>
          None
      }
    }.toList

    context.reporter.info(s"Preparing Isabelle setup (this might take a while) ...")
    val setup = Setup.default(version) match {
      case Left(reason) => context.reporter.fatalError(s"Isabelle setup failed: ${reason.explain}")
      case Right(setup) => setup
    }

    val resources = Resources.dumpIsabelleResources() match {
      case Left(reason) => context.reporter.fatalError(s"Resource dump failed: ${reason.explain}")
      case Right(resources) => resources
    }

    val config = Configuration.simple("Leon")
    val system = setup.makeEnvironment(resources).flatMap { env =>
      context.reporter.info(s"Building session ...")
      if (!System.build(env, config))
        context.reporter.internalError("Build failed")

      context.reporter.info(s"Starting $version instance ...")
      System.create(env, config)
    }

    val thy = system.flatMap { system =>
      context.reporter.debug(s"Loading theory as $theory ...")

      system.invoke(Load)(("Leon", theory, scripts)).assertSuccess(context).map {
        case Nil =>
          ()
        case bad =>
          context.reporter.fatalError(s"Could not process the following scripts: ${bad.mkString(", ")}")
      }
    }

    val oracle =
      if (strict) {
        context.reporter.debug("Strict mode enabled; background proofs will be replayed in Isabelle")
        Future.successful { () }
      }
      else {
        context.reporter.warning("Strict mode disabled; proofs may be unsound")
        thy.flatMap(_ => system.flatMap(_.invoke(Oracle)(()))).assertSuccess(context)
      }

    val types =
      for {
        s <- system
        () <- thy
        _ = context.reporter.debug(s"Defining types ...")
      }
      yield
        new Types(context, program, s)

    val functions =
      for {
        s <- system
        t <- types
        () <- oracle
        _ <- t.data
      }
      yield
        new Functions(context, program, t, funs, s)

    val output =
      for {
        s <- system
        f <- functions
        d <- f.data
      }
      yield {
        if (dump.isEmpty)
          s.invoke(Report)(()).assertSuccess(context).map { report =>
            context.reporter.debug(s"Report for $theory ...")
            report.foreach { case (key, value) =>
              context.reporter.debug(s"$key: ${canonicalizeOutput(s, value)}")
            }
          }
        else
          s.invoke(Dump)(()).assertSuccess(context).map { output =>
            context.reporter.debug(s"Dumping theory sources to $dump ...")
            val path = Files.createDirectories(Paths.get(dump))
            output.foreach { case (name, content) =>
              val writer = new FileWriter(path.resolve(s"$name.thy").toFile())
              writer.write(content)
              writer.close()
            }
          }
      }

    for {
      s <- system
      t <- types
      f <- functions
      _ <- t.data
      _ <- f.data
      _ <- output
    }
    yield new IsabelleEnvironment(context, program, t, f, s, funs)
  }

}

final class IsabelleEnvironment private(
    val context: LeonContext,
    val program: Program,
    val types: Types,
    val functions: Functions,
    val system: System,
    val selectedFunDefs: List[FunDef]
) {
  def solver: IsabelleSolver with TimeoutSolver =
    new IsabelleSolver(context.toSctx, program, types, functions, system) with TimeoutSolver
}
