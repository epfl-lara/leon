/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package repair

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.DefOps._
import purescala.Constructors._
import purescala.ScalaPrinter
import evaluators._
import datagen._
import solvers._
import utils._
import solvers.z3._
import codegen._
import verification._
import synthesis._
import synthesis.rules._
import synthesis.heuristics._
import graph.DotGenerator

class Repairman(ctx: LeonContext, program: Program, fd: FunDef, verifTimeout: Option[Long]) {
  val reporter = ctx.reporter

  implicit val debugSection = DebugSectionRepair

  def getSynthesizer(tests: List[Example]): Synthesizer = {
    // Gather in/out tests
    val pre = fd.precondition.getOrElse(BooleanLiteral(true))
    val args = fd.params.map(_.id)
    val argsWrapped = tupleWrap(args.map(_.toVariable))

    // Compute tests
    val out = fd.postcondition.map(_._1).getOrElse(FreshIdentifier("res", true).setType(fd.returnType))

    val testsCases = tests.collect {
      case InOutExample(ins, outs) =>
        val (patt, optGuard) = expressionToPattern(tupleWrap(ins))
        MatchCase(patt, optGuard match {
          case BooleanLiteral(true) => None
          case guard => Some(guard)
        }, tupleWrap(outs))
    }.toList

    val passes = if (testsCases.nonEmpty) {
      Passes(argsWrapped, out.toVariable, testsCases)
    } else {
      BooleanLiteral(true)
    }

    // Create a fresh function
    val nid = FreshIdentifier(fd.id.name+"_repair").copiedFrom(fd.id)
    val nfd = new FunDef(nid, fd.tparams, fd.returnType, fd.params, fd.defType)
    nfd.copyContentFrom(fd)
    nfd.copiedFrom(fd)

    nfd.body = nfd.body.map { b => preMap({
      case fi @ FunctionInvocation(TypedFunDef(`fd`, tps), args) =>
        Some(FunctionInvocation(TypedFunDef(nfd, tps), args).copiedFrom(fi))
      case _ => None
    })(b)}

    val spec = and(
      nfd.postcondition.map(_._2).getOrElse(BooleanLiteral(true)),
      passes
    )

    val p = focusRepair(tests, nfd, spec, out)

    val soptions0 = SynthesisPhase.processOptions(ctx);

    val soptions = soptions0.copy(
      costModel = RepairCostModel(soptions0.costModel),
      rules = (soptions0.rules ++ Seq(
        GuidedDecomp,
        GuidedCloser,
        CEGLESS
      )) diff Seq(ADTInduction)
    );

    new Synthesizer(ctx, nfd, program, p, soptions)
  }

  private def guideOf(expr: Expr): Expr = {
    val gfd = program.library.guide.get.typed(Seq(expr.getType))
    FunctionInvocation(gfd, Seq(expr))
  }

  private def focusRepair(tests: List[Example], fd: FunDef, post: Expr, out: Identifier): Problem = {
    reporter.ifDebug { printer =>
      printer("Tests failing are: ")
      tests.collect {
        case InExample(ins) =>
          printer(ins.mkString(", "))
      }
    }

    // Compute initial call for terminating argument
    val termfd = program.library.terminating.get
    val withinCall = FunctionInvocation(fd.typedWithDef, fd.params.map(_.id.toVariable))
    val terminating = FunctionInvocation(termfd.typed(Seq(fd.returnType)), Seq(withinCall))

    val pre = fd.precondition.getOrElse(BooleanLiteral(true))

    val body = fd.body.get

    val ws = and(
      guideOf(body),
      terminating
    )

    // Synthesis from the ground up
    val p = Problem(fd.params.map(_.id).toList, ws, pre, post, List(out))

    p
  }

  def getVerificationCounterExamples(fd: FunDef, prog: Program): Option[Seq[InExample]] = {
    val timeoutMs = verifTimeout.getOrElse(3000L)
    val solverf = SolverFactory(() => (new FairZ3Solver(ctx, prog) with TimeoutSolver).setTimeout(timeoutMs))
    val vctx = VerificationContext(ctx, prog, solverf, reporter)
    val vcs = AnalysisPhase.generateVerificationConditions(vctx, Some(List(fd.id.name)))

    AnalysisPhase.checkVerificationConditions(vctx, vcs)

    var invalid = false;
    var ces = List[Seq[Expr]]()

    for (vc <- vcs.getOrElse(fd, List())) {
      if (vc.value == Some(false)) {
        invalid = true;

        vc.counterExample match {
          case Some(m) =>
            ces = fd.params.map(vd => m(vd.id)) :: ces;

          case _ =>
        }
      }
    }
    if (invalid) {
      Some(ces.map(InExample(_)))
    } else {
      None
    }
  }


  def discoverTests: List[Example] = {
    val evaluator = new CodeGenEvaluator(ctx, program, CodeGenParams(checkContracts = true))
    val generator= new NaiveDataGen(ctx, program, evaluator)

    val pre = fd.precondition.getOrElse(BooleanLiteral(true))

    val inputs = generator.generateFor(fd.params.map(_.id), pre, 30, 10000).toList

    var tests = List[Example]()

    tests ++= inputs.map { i =>
      evaluator.eval(FunctionInvocation(fd.typed(fd.tparams.map(_.tp)), i)) match {
        case EvaluationResults.Successful(res) =>
          new InOutExample(i, List(res))

        case _ =>
          new InExample(i)
      }
    }

    // Try to verify, if it fails, we have at least one CE
    getVerificationCounterExamples(fd, program) match {
      case Some(ces) =>
        tests ++= ces
      case _ =>
    }

    tests
  }

  def repair() = {
    reporter.info(ASCIIHelpers.title("1. Discovering tests for "+fd.id))
    val tests = discoverTests

    reporter.info(ASCIIHelpers.title("2. Creating synthesis Problem"))
    val synth = getSynthesizer(tests)
    val p     = synth.problem

    var solutions = List[Solution]()

    reporter.info(ASCIIHelpers.title("3. Synthesizing"))
    reporter.info(p)

    synth.synthesize() match {
      case (search, sols) =>
        for (sol <- sols) {

          // Validate solution if not trusted
          if (!sol.isTrusted) {
            reporter.info("Found untrusted solution! Verifying...")
            val (npr, fds) = synth.solutionToProgram(sol)

            getVerificationCounterExamples(fds.head, npr) match {
              case Some(ces) =>
                reporter.error("I ended up finding this counter example:\n"+ces.mkString("  |  "))

              case None =>
                solutions ::= sol
                reporter.info("Solution was not trusted but verification passed!")
            }
          } else {
            reporter.info("Found trusted solution!")
            solutions ::= sol
          }
        }

        if (synth.options.generateDerivationTrees) {
          val dot = new DotGenerator(search.g)
          dot.writeFile("derivation"+DotGenerator.nextId()+".dot")
        }

        if (solutions.isEmpty) {
          reporter.error(ASCIIHelpers.title("Failed to repair!"))
        } else {
          reporter.info(ASCIIHelpers.title("Repair successful:"))
          for ((sol, i) <- solutions.zipWithIndex) {
            reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+":"))
            val expr = sol.toSimplifiedExpr(ctx, program)
            reporter.info(ScalaPrinter(expr));
          }
        }
      }
  }

  // ununsed for now, but implementation could be useful later
  private def disambiguate(p: Problem, sol1: Solution, sol2: Solution): Option[(InOutExample, InOutExample)] = {
    val s1 = sol1.toSimplifiedExpr(ctx, program)
    val s2 = sol2.toSimplifiedExpr(ctx, program)

    val e = new DefaultEvaluator(ctx, program);

    def unwrap(e: Expr) = if (p.xs.size > 1) {
      val Tuple(es) = e
      es
    } else {
      Seq(e)
    }

    if (s1 == s2) {
      None
    } else {
      val diff = and(p.pc, not(Equals(s1, s2)))
      val solver = (new FairZ3Solver(ctx, program) with TimeoutSolver).setTimeout(1000)

      solver.assertCnstr(diff)
      solver.check match {
        case Some(true) =>
          val m = solver.getModel
          val inputs = p.as.map(id => m.getOrElse(id, simplestValue(id.getType)))
          val inputsMap = (p.as zip inputs).toMap

          (e.eval(s1, inputsMap), e.eval(s2, inputsMap)) match {
            case (EvaluationResults.Successful(r1), EvaluationResults.Successful(r2)) =>
              Some((InOutExample(inputs, unwrap(r1)), InOutExample(inputs, unwrap(r2))))
            case _ =>
              None
          }
        case Some(false) =>
          None
        case _ =>
          // considered as equivalent
          None
      }
    }
  }
}
