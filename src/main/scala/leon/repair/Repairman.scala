/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package repair

import purescala.Path
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors._

import evaluators._
import solvers._
import utils._
import codegen._
import verification._
import datagen.GrammarDataGen

import synthesis._
import synthesis.rules._
import synthesis.Witnesses._
import synthesis.graph.{dotGenIds, DotGenerator}

import rules._

class Repairman(ctx: LeonContext, program: Program, fd: FunDef, verifTimeoutMs: Option[Long], repairTimeoutMs: Option[Long]) {
  implicit val ctx0 = ctx

  val reporter = ctx.reporter

  val doBenchmark = ctx.findOptionOrDefault(GlobalOptions.optBenchmark)

  implicit val debugSection = DebugSectionRepair

  def repair(): Unit = {
    val to = new TimeoutFor(ctx.interruptManager)

    to.interruptAfter(repairTimeoutMs) {
      reporter.info(ASCIIHelpers.title("1. Discovering tests for "+fd.id))

      val timer = new Timer().start

      val eb = discoverTests()

      if (eb.invalids.nonEmpty) {
        reporter.info(f" - Passing: ${eb.valids.size}%3d")
        reporter.info(f" - Failing: ${eb.invalids.size}%3d")

        reporter.ifDebug { printer =>
          printer(eb.asString("Discovered Tests"))
        }

        reporter.info(ASCIIHelpers.title("2. Minimizing tests"))
        val eb2 = eb.minimizeInvalids(fd, ctx, program)

        // We exclude redundant failing tests, and only select the minimal tests
        reporter.info(f" - Minimal Failing Set Size: ${eb2.invalids.size}%3d")

        reporter.ifDebug { printer =>
          printer(eb2.asString("Minimal Failing Tests"))
        }

        val timeTests = timer.stop
        timer.start

        val synth = getSynthesizer(eb2)

        try {
          reporter.info(ASCIIHelpers.title("3. Synthesizing repair"))
          val (search0, sols0) = synth.synthesize()

          val timeSynth = timer.stop
          timer.start

          val (search, solutions) = synth.validate((search0, sols0), allowPartial = false)

          val timeVerify = timer.stop

          if (doBenchmark) {
            val be = BenchmarkEntry.fromContext(ctx) ++ Map(
              "function"          -> fd.id.name,
              "time_tests"        -> timeTests,
              "time_synthesis"    -> timeSynth,
              "time_verification" -> timeVerify,
              "success"           -> solutions.nonEmpty,
              "verified"          -> solutions.forall(_._2)
            )

            val bh = new BenchmarksHistory("repairs.dat")

            bh += be

            bh.write()
          }

          reporter.ifDebug { printer =>
            import java.text.SimpleDateFormat
            import java.util.Date

            val categoryName = fd.getPos.file.toString.split("/").dropRight(1).lastOption.getOrElse("?")
            val benchName = categoryName+"."+fd.id.name

            val defs = visibleFunDefsFromMain(program).collect {
              case fd: FunDef => 1 + fd.params.size + formulaSize(fd.fullBody)
            }

            val pSize = defs.sum
            val fSize = formulaSize(fd.body.get)

            def localizedExprs(n: graph.Node): List[Expr] = {
              n match {
                case on: graph.OrNode =>
                  on.selected.flatMap(localizedExprs)
                case an: graph.AndNode if an.ri.rule == Focus =>
                  an.selected.flatMap(localizedExprs)
                case an: graph.AndNode =>
                  val TopLevelAnds(clauses) = an.p.ws

                  val res = clauses.collect {
                    case Guide(expr) => expr
                  }

                  res.toList
              }
            }

            val locSize = localizedExprs(search.g.root).map(formulaSize).sum

            val (solSize, proof) = solutions.headOption match {
              case Some((sol, trusted)) =>
                val solExpr = sol.toSimplifiedExpr(ctx, program, fd)
                val totalSolSize = formulaSize(solExpr)
                (locSize+totalSolSize-fSize, if (trusted) "$\\chmark$" else "")
              case _ =>
                (0, "X")
            }

            val date = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date())

            val fw = new java.io.FileWriter("repair-report.txt", true)

            try {
              fw.write(f"$date:  $benchName%-30s & $pSize%4d & $fSize%4d & $locSize%4d & $solSize%4d & ${timeTests/1000.0}%2.1f &  ${timeSynth/1000.0}%2.1f & $proof%7s \\\\\n")
            } finally {
              fw.close()
            }
          }(DebugSectionReport)

          if (synth.settings.generateDerivationTrees) {
            val dot = new DotGenerator(search)
            dot.writeFile("derivation"+ dotGenIds.nextGlobal + ".dot")
          }

          if (solutions.isEmpty) {
            reporter.error(ASCIIHelpers.title("Failed to repair!"))
          } else {

            reporter.info(ASCIIHelpers.title("Repair successful:"))
            for ( ((sol, isTrusted), i) <- solutions.zipWithIndex) {
              reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+ (if(isTrusted) "" else " (untrusted)" ) + ":"))
              val expr = sol.toSimplifiedExpr(ctx, synth.program, fd)
              reporter.info(expr.asString(program)(ctx))
            }
          }
        } finally {
          synth.shutdown()
        }
      } else {
        reporter.info(s"Could not find a wrong execution.")
      }
    }
  }

  def getSynthesizer(eb: ExamplesBank): Synthesizer = {

    val origBody = fd.body.get

    val term  = Terminating(fd.applied)
    val guide = Guide(origBody)
    val pre   = fd.precOrTrue

    val prob = Problem.fromSpec(fd.postOrTrue, Path(Seq(pre, guide, term)), eb, Some(fd))

    val ci = SourceInfo(fd, origBody, prob)

    // Return synthesizer for this choose
    val so0 = SynthesisPhase.processOptions(ctx)

    val soptions = so0.copy(
      functionsToIgnore = so0.functionsToIgnore + fd,
      rules = Seq(Focus, CEGLESS) ++ so0.rules
    )

    new Synthesizer(ctx, program, ci, soptions)
  }

  def getVerificationCExs(fd: FunDef): Seq[Example] = {
    val timeoutMs = verifTimeoutMs.getOrElse(3000L)
    val solverf = SolverFactory.getFromSettings(ctx, program).withTimeout(timeoutMs)
    val vctx = new VerificationContext(ctx, program, solverf)
    val vcs = VerificationPhase.generateVCs(vctx, Seq(fd))

    try {
      val report = VerificationPhase.checkVCs(
        vctx,
        vcs,
        stopWhen = _.isInvalid
      )

      val vrs = report.vrs

      vrs.collect { case (_, VCResult(VCStatus.Invalid(ex), _, _)) =>
        InExample(fd.paramIds map ex)
      }
    } finally {
      solverf.shutdown()
    }
  }

  def discoverTests(): ExamplesBank = {

    val maxEnumerated = 1000
    val maxValid      = 400

    val evaluator = new CodeGenEvaluator(ctx, program)

    val inputsToExample: Seq[Expr] => Example = { ins =>
      evaluator.eval(functionInvocation(fd, ins)) match {
        case EvaluationResults.Successful(res) =>
          new InOutExample(ins, List(res))
        case _ =>
          new InExample(ins)
      }
    }

    val dataGen = new GrammarDataGen(evaluator)

    val generatedTests = dataGen
      .generateFor(fd.paramIds, fd.precOrTrue, maxValid, maxEnumerated)
      .map(inputsToExample)
      .toList

    val (genPassing, genFailing) = generatedTests.partition {
      case _: InOutExample => true
      case _               => false
    }

    val genTb = ExamplesBank(genPassing, genFailing).stripOuts

    // Extract passing/failing from the passes in POST
    val userTb = new ExamplesFinder(ctx, program).extractFromFunDef(fd, partition = true)

    val allTb = genTb union userTb

    if (allTb.invalids.isEmpty) {
      ExamplesBank(allTb.valids, getVerificationCExs(fd))
    } else {
      allTb
    }
  }

  def programSize(pgm: Program): Int = {
    visibleFunDefsFromMain(pgm).foldLeft(0) {
      case (s, f) => 
        1 + f.params.size + formulaSize(f.fullBody) + s
    }
  }
}
