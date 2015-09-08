package leon.solvers.isabelle

import java.io.FileWriter
import java.nio.file.{Files, Paths}

import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

import leon.LeonContext
import leon.OptionsHelpers._
import leon.SharedOptions
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Common._
import leon.solvers._
import leon.utils._

import edu.tum.cs.isabelle.{impl => impl2015, _}
import edu.tum.cs.isabelle.api._
import edu.tum.cs.isabelle.setup._

object IsabelleEnvironment {

  private implicit val debugSection = DebugSectionIsabelle

  def apply(context: LeonContext, program: Program): Future[IsabelleEnvironment] = {
    val version = Version(isabelleVersion)
    val base = Paths.get(context.findOptionOrDefault(Component.optBase))
    val download = context.findOptionOrDefault(Component.optDownload)
    val build = context.findOptionOrDefault(Component.optBuild)
    val dump = context.findOptionOrDefault(Component.optDump)
    val strict = context.findOptionOrDefault(Component.optStrict)

    val funFilter =
      // FIXME duplicated from AnalysisPhase
      filterInclusive[FunDef](context.findOption(SharedOptions.optFunctions).map(fdMatcher(program)), Some(_.annotations contains "library"))

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

    val setup = Setup.detectSetup(base, version) match {
      case Some(setup) => Future.successful { setup }
      case None if !download =>
        context.reporter.fatalError(s"No $version found at $base. Please install manually or set '${Component.optDownload.name}' flag to true.")
      case _ =>
        context.reporter.info(s"No $version found at $base")
        context.reporter.info(s"Preparing $version environment ...")
        Setup.installTo(Files.createDirectories(base), version)
    }

    val system = setup.flatMap { setup =>
      val env = new impl2015.Environment(setup.home)
      val config = env.Configuration.fromPath(Component.leonBase, "Leon")

      if (build) {
        context.reporter.info(s"Building session ...")
        if (!System.build(env)(config))
          context.reporter.internalError("Build failed")
      }

      context.reporter.info(s"Starting $version instance ...")
      System.create(env)(config)
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

    functions.flatMap(_.data).foreach { _ =>
      if (dump.isEmpty)
        system.flatMap(_.invoke(Report)(())).assertSuccess(context).foreach { report =>
          context.reporter.debug(s"Report for $theory ...")
          report.foreach { case (key, value) =>
            context.reporter.debug(s"$key: ${canonicalizeOutput(value)}")
          }
        }
      else
        system.flatMap(_.invoke(Dump)(())).assertSuccess(context).foreach { output =>
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
    new IsabelleSolver(context, program, types, functions, system) with TimeoutSolver
}
