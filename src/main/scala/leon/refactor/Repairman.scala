/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package refactor

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

class Repairman(ctx: LeonContext, program: Program, fd: FunDef) {
  val reporter = ctx.reporter

  implicit val debugSection = DebugSectionRefactor

  var testBank = List[Example]()

  var solutions: List[(Solution, Expr, List[FunDef])] = Nil

  def repair(): Unit = {
    // Gather in/out tests
    val pre = fd.precondition.getOrElse(BooleanLiteral(true))
    val args = fd.params.map(_.id)
    val argsWrapped = tupleWrap(args.map(_.toVariable))

    // Compute tests
    val out = fd.postcondition.map(_._1).getOrElse(FreshIdentifier("res", true).setType(fd.returnType))

    val tfd = program.library.passes.get.typed(Seq(argsWrapped.getType, out.getType))

    val inouts = testBank;

    val testsExpr = FiniteMap(inouts.collect {
      case InOutExample(ins, outs) =>
        tupleWrap(ins) -> tupleWrap(outs)
    }.toList).setType(MapType(argsWrapped.getType, out.getType))

    val passes = if (testsExpr.singletons.nonEmpty) {
      FunctionInvocation(tfd, Seq(argsWrapped, out.toVariable, testsExpr))
    } else {
      BooleanLiteral(true)
    }

    // Compute guide implementation
    val gexpr = fd.body.get
    val gfd = program.library.guide.get.typed(Seq(gexpr.getType))
    val guide = FunctionInvocation(gfd, Seq(gexpr))

    // Compute initial call
    val termfd = program.library.terminating.get
    val withinCall = FunctionInvocation(fd.typedWithDef, fd.params.map(_.id.toVariable))
    val terminating = FunctionInvocation(termfd.typed(Seq(fd.returnType)), Seq(withinCall))

    val spec = And(Seq(
      fd.postcondition.map(_._2).getOrElse(BooleanLiteral(true)),
      passes
    ))

    val pc = And(Seq(
      pre,
      guide,
      terminating
    ))

    // Synthesis from the ground up
    val p = Problem(fd.params.map(_.id).toList, pc, spec, List(out))
    val ch = Choose(List(out), spec)
    fd.body = Some(ch)

    val soptions0 = SynthesisPhase.processOptions(ctx);

    val soptions = soptions0.copy(
      costModel = RepairCostModel(soptions0.costModel),
      rules = (soptions0.rules ++ Seq(
        GuidedDecomp,
        GuidedCloser,
        CEGLESS
      )) diff Seq(ADTInduction)
    );

    val synthesizer = new Synthesizer(ctx, fd, program, p, soptions)

    synthesizer.synthesize() match {
      case (search, sols) =>
        for (sol <- sols) {
          val expr = sol.toSimplifiedExpr(ctx, program)

          val (npr, fds) = synthesizer.solutionToProgram(sol)

          if (!sol.isTrusted) {
            getVerificationCounterExamples(fds.head, npr) match {
              case Some(ces) =>
                testBank ++= ces
                reporter.info("Failed :(, but I learned: "+ces.mkString("  |  "))
              case None =>
                solutions ::= (sol, expr, fds)
                reporter.info(ASCIIHelpers.title("ZUCCESS!"))
            }
          } else {
            solutions ::= (sol, expr, fds)
            reporter.info(ASCIIHelpers.title("ZUCCESS!"))
          }
        }

        if (soptions.generateDerivationTrees) {
          val dot = new DotGenerator(search.g)
          dot.writeFile("derivation"+DotGenerator.nextId()+".dot")
        }

        if (solutions.isEmpty) {
            reporter.info(ASCIIHelpers.title("FAILURZ!"))
        } else {
          reporter.info(ASCIIHelpers.title("Solutions"))
          for (((sol, expr, fds), i) <- solutions.zipWithIndex) {
            reporter.info(ASCIIHelpers.subTitle("Solution "+(i+1)+":"))
            reporter.info(ScalaPrinter(expr));
          }

          if (solutions.size > 1) {
            reporter.info(ASCIIHelpers.title("Disambiguating..."))
            disambiguate(p, solutions(0)._1, solutions(1)._1) match {
              case Some((o1, o2)) =>
                reporter.info("Solutions differ on "+o1.ins.mkString(", "))
                reporter.info("solution A produces: "+o1.outs.mkString(", "))
                reporter.info("solution B produces: "+o2.outs.mkString(", "))
  
              case None =>
                reporter.info("Solutions appear equivalent..")
            }
          }
        }

      case _ =>
        reporter.error("I failed you :(")
    }

  }

  def getVerificationCounterExamples(fd: FunDef, prog: Program): Option[Seq[InExample]] = {
    val timeoutMs = 3000l
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

  def disambiguate(p: Problem, sol1: Solution, sol2: Solution): Option[(InOutExample, InOutExample)] = {
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
      val diff = And(p.pc, Not(Equals(s1, s2)))
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

  def classifier(ok: Seq[Example], notok: Seq[Example]): Option[Expr] = {
    // Obtain expr that returns partitions all examples into ok/notok

    None
  }

  def discoverTests() = {
    val evaluator = new CodeGenEvaluator(ctx, program, CodeGenParams(checkContracts = true))
    val tests = new NaiveDataGen(ctx, program, evaluator)

    val pre = fd.precondition.getOrElse(BooleanLiteral(true))

    val inputs = tests.generateFor(fd.params.map(_.id), pre, 30, 10000).toList

    testBank ++= inputs.map { i =>
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
        testBank ++= ces
      case _ =>
    }
  }

  discoverTests()

}
