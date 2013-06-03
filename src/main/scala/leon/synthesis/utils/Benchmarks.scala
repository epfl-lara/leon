/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.utils

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._

import java.util.Date
import java.text.SimpleDateFormat

import sys.process._

import java.io.File

object Benchmarks extends App {

  val allRules = Rules.all ++ Heuristics.all

  var rule: Rule = rules.CEGIS

  // Parse arguments
  val (options, others) = args.partition(_.startsWith("--"))

  val newOptions = options flatMap {
    case setting if setting.startsWith("--rule=") =>
      val name = setting.drop(7)

      allRules.find(_.name.toLowerCase == name.toLowerCase) match {
        case Some(r) =>
          rule = r
        case None =>
          println("Could not find rule: "+name)
          println("Available rules: ")
          for (r <- allRules) {
            println(" - "+r.name)
          }
          sys.exit(1);
      }

      None

    case setting =>
      Some(setting)
  }

  println("# Date: "+new SimpleDateFormat("dd.MM.yyyy HH:mm:ss").format(new Date()))
  println("# Git tree: "+("git log -1 --format=\"%H\"".!!).trim)
  println("# Using rule: "+rule.name)


  val infoSep    : String = "╟" + ("┄" * 86) + "╢"
  val infoFooter : String = "╚" + ("═" * 86) + "╝"
  val infoHeader : String = "  ┌────────────┐\n" +
                            "╔═╡ Benchmarks ╞" + ("═" * 71) + "╗\n" +
                            "║ └────────────┘" + (" " * 71) + "║"

  def infoLine(file: String, f: String, ts: Long, nAlt: Int, nSuccess: Int, nInnap: Int, nDecomp: Int) : String = {
    "║ %-30s %-24s %3d %10s %10s ms ║".format(
      file,
      f,
      nAlt,
      nSuccess+"/"+nInnap+"/"+nDecomp,
      ts)
  }

  println(infoHeader)

  var nSuccessTotal, nInnapTotal, nDecompTotal, nAltTotal = 0
  var tTotal: Long = 0

  val ctx = leon.Main.processOptions(new DefaultReporter, others ++ newOptions)

  for (file <- ctx.files) {
    val innerCtx = ctx.copy(files = List(file))

    val opts = SynthesisOptions()

    val pipeline = leon.plugin.ExtractionPhase andThen SynthesisProblemExtractionPhase

    val (program, results) = pipeline.run(innerCtx)(file.getPath :: Nil)

    val solver = new FairZ3Solver(ctx.copy(reporter = new SilentReporter))
    solver.setProgram(program)

    val simpleSolver = new UninterpretedZ3Solver(ctx.copy(reporter = new SilentReporter))
    simpleSolver.setProgram(program)

    for ((f, ps) <- results.toSeq.sortBy(_._1.id.toString); p <- ps) {
      val sctx = SynthesisContext(
        context         = ctx,
        options         = opts,
        functionContext = Some(f),
        program         = program,
        solver          = solver,
        simpleSolver    = simpleSolver,
        reporter        = new DefaultReporter,
        shouldStop      = new java.util.concurrent.atomic.AtomicBoolean
      )

      val ts = System.currentTimeMillis

      val rr = rule.instantiateOn(sctx, p)

      val nAlt = rr.size
      var nSuccess, nInnap, nDecomp = 0

      for (alt <- rr) {
        alt.apply(sctx) match {
          case RuleApplicationImpossible =>
            nInnap += 1
          case s: RuleDecomposed =>
            nDecomp += 1
          case s: RuleSuccess =>
            nSuccess += 1
        }
      }

      val t = System.currentTimeMillis - ts

      nAltTotal     += nAlt
      tTotal        += t
      nSuccessTotal += nSuccess
      nInnapTotal   += nInnap
      nDecompTotal  += nDecomp

      println(infoLine(file.getName().toString, f.id.toString, t, nAlt, nSuccess, nInnap, nDecomp))
    }

    println(infoSep)

  }

  println(infoLine("TOTAL", "", tTotal, nAltTotal, nSuccessTotal, nInnapTotal, nDecompTotal))

  println(infoFooter)

  println

  val infoHeader2 : String = "  ┌────────────┐\n" +
                             "╔═╡ Timers     ╞" + ("═" * 71) + "╗\n" +
                             "║ └────────────┘" + (" " * 71) + "║"

  println(infoHeader2)
  for ((name, sw) <- StopwatchCollections.getAll.toSeq.sortBy(_._1)) {
    println("║ %-70s %10s ms ║".format(name, sw.getMillis))
  }
  println(infoFooter)
}
