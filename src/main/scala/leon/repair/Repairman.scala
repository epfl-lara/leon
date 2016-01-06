/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.DefOps._
import purescala.Constructors._
import purescala.Extractors.unwrapTuple

import evaluators._
import solvers._
import utils._
import codegen._
import verification._

import synthesis._
import synthesis.rules._
import synthesis.Witnesses._
import synthesis.graph.{dotGenIds, DotGenerator}

import rules._
import grammars._

class Repairman(ctx0: LeonContext, initProgram: Program, fd: FunDef, verifTimeoutMs: Option[Long], repairTimeoutMs: Option[Long]) {
  implicit val ctx = ctx0

  val reporter = ctx.reporter

  val doBenchmark = ctx.findOptionOrDefault(SharedOptions.optBenchmark)

  var program = initProgram

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
            import java.io.FileWriter
            import java.text.SimpleDateFormat
            import java.util.Date

            val categoryName = fd.getPos.file.toString.split("/").dropRight(1).lastOption.getOrElse("?")
            val benchName = categoryName+"."+fd.id.name

            val defs = visibleFunDefsFromMain(program).collect {
              case fd: FunDef => 1 + fd.params.size + formulaSize(fd.fullBody)
            }

            val pSize = defs.sum;
            val fSize = formulaSize(fd.body.get)

            def localizedExprs(n: graph.Node): List[Expr] = {
              n match {
                case on: graph.OrNode =>
                  on.selected.map(localizedExprs).flatten
                case an: graph.AndNode if an.ri.rule == Focus =>
                  an.selected.map(localizedExprs).flatten
                case an: graph.AndNode =>
                  val TopLevelAnds(clauses) = an.p.ws

                  val res = clauses.collect {
                    case Guide(expr) => expr
                  }

                  res.toList
              }
            }

            val locSize = localizedExprs(search.g.root).map(formulaSize).sum;

            val (solSize, proof) = solutions.headOption match {
              case Some((sol, trusted)) =>
                val solExpr = sol.toSimplifiedExpr(ctx, program)
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
              fw.close
            }
          }(DebugSectionReport)

          if (synth.settings.generateDerivationTrees) {
            val dot = new DotGenerator(search.g)
            dot.writeFile("derivation"+ dotGenIds.nextGlobal + ".dot")
          }

          if (solutions.isEmpty) {
            reporter.error(ASCIIHelpers.title("Failed to repair!"))
          } else {

            reporter.info(ASCIIHelpers.title("Repair successful:"))
            for ( ((sol, isTrusted), i) <- solutions.zipWithIndex) {
              reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+ (if(isTrusted) "" else " (untrusted)" ) + ":"))
              val expr = sol.toSimplifiedExpr(ctx, synth.program)
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

    val term  = Terminating(fd.typed, fd.params.map(_.id.toVariable))
    val guide = Guide(origBody)
    val pre   = fd.precOrTrue

    val ci = SourceInfo(
      fd = fd,
      pc = andJoin(Seq(pre, guide, term)),
      source = origBody,
      spec = fd.postOrTrue,
      eb = eb
    )

    // Return synthesizer for this choose
    val so0 = SynthesisPhase.processOptions(ctx)

    val soptions = so0.copy(
      functionsToIgnore = so0.functionsToIgnore + fd,
      costModel = RepairCostModel(so0.costModel),
      rules = (so0.rules ++ Seq(
        Focus,
        CEGLESS
        //TEGLESS
      )) diff Seq(ADTInduction, TEGIS, IntegerInequalities, IntegerEquation)
    )

    new Synthesizer(ctx, program, ci, soptions)
  }

  def getVerificationCExs(fd: FunDef): Seq[Example] = {
    val timeoutMs = verifTimeoutMs.getOrElse(3000L)
    val solverf = SolverFactory.getFromSettings(ctx, program).withTimeout(timeoutMs)
    val vctx = VerificationContext(ctx, program, solverf, reporter)
    val vcs = VerificationPhase.generateVCs(vctx, Seq(fd))

    try {
      val report = VerificationPhase.checkVCs(
        vctx,
        vcs,
        stopAfter = Some({ (vc, vr) => vr.isInvalid })
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

    import bonsai.enumerators._

    val maxEnumerated = 1000
    val maxValid      = 400

    val evaluator = new CodeGenEvaluator(ctx, program, CodeGenParams.default)
    val enum      = new MemoizedEnumerator[TypeTree, Expr](ValueGrammar.getProductions)

    val inputs = enum.iterator(tupleTypeWrap(fd.params map { _.getType})).map(unwrapTuple(_, fd.params.size))

    val filtering: Seq[Expr] => Boolean = fd.precondition match {
      case None =>
        _ => true
      case Some(pre) =>
        val argIds = fd.paramIds
        evaluator.compile(pre, argIds) match {
          case Some(evalFun) =>
            val sat = EvaluationResults.Successful(BooleanLiteral(true));
            { (es: Seq[Expr]) => evalFun(new solvers.Model((argIds zip es).toMap)) == sat }
          case None =>
            { _ => false }
        }
    }

    val inputsToExample: Seq[Expr] => Example = { ins =>
      evaluator.eval(functionInvocation(fd, ins)) match {
        case EvaluationResults.Successful(res) =>
          new InOutExample(ins, List(res))
        case _ =>
          new InExample(ins)
      }
    }

    val generatedTests = inputs
      .take(maxEnumerated)
      .filter(filtering)
      .take(maxValid)
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
