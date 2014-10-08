/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package refactor

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
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

class Repairman(ctx: LeonContext, program: Program, fd: FunDef) {
  val reporter = ctx.reporter

  var testBank = List[Example]()

  var solutions: List[(Solution, Expr, List[FunDef])] = Nil

  def repair(): Unit = {
    // Gather in/out tests
    val pre = fd.precondition.getOrElse(BooleanLiteral(true))
    val args = fd.params.map(_.id)
    val argsWrapped = tupleWrap(args.map(_.toVariable))

    val out = fd.postcondition.map(_._1).getOrElse(FreshIdentifier("res", true).setType(fd.returnType))

    val tfd = program.library.passes.get.typed(Seq(argsWrapped.getType, out.getType))

    val inouts = testBank;

    val testsExpr = FiniteMap(inouts.collect {
      case InOutExample(ins, outs) =>
        tupleWrap(ins) -> tupleWrap(outs)
    }.toList).setType(MapType(argsWrapped.getType, out.getType))

    val passes = FunctionInvocation(tfd, Seq(argsWrapped, out.toVariable, testsExpr))

    val spec = And(fd.postcondition.map(_._2).getOrElse(BooleanLiteral(true)), passes)

    // Synthesis from the ground up
    val p = Problem(fd.params.map(_.id).toList, pre, spec, List(out))

    val soptions = SynthesisPhase.processOptions(ctx);

    val synthesizer = new Synthesizer(ctx, fd, program, p, soptions)

    synthesizer.synthesize() match {
      case (search, sols) =>
        for (sol <- sols) {
          val expr = sol.toSimplifiedExpr(ctx, program)

          val (npr, fds) = synthesizer.solutionToProgram(sol)
          solutions ::= (sol, expr, fds)

          if (!sol.isTrusted) {

            val timeoutMs = 3000l
            val solverf = SolverFactory(() => (new FairZ3Solver(ctx, npr) with TimeoutSolver).setTimeout(timeoutMs))
            val vctx = VerificationContext(ctx, npr, solverf, reporter)
            val nfd = fds.head
            val vcs = AnalysisPhase.generateVerificationConditions(vctx, Some(List(nfd.id.name)))

            AnalysisPhase.checkVerificationConditions(vctx, vcs)

            var unknown = false;
            var ces = List[Seq[Expr]]()

            for (vc <- vcs.getOrElse(nfd, List())) {
              if (vc.value == Some(false)) {
                vc.counterExample match {
                  case Some(m) =>
                    ces = nfd.params.map(vd => m(vd.id)) :: ces;

                  case _ =>
                }
              } else if (vc.value == None) {
                unknown = true;
              }
            }


            if (ces.isEmpty) {
              if (!unknown) {
                reporter.info("ZZUCCESS!")
              } else {
                reporter.info("ZZUCCESS (maybe)!")
              }
            } else {
              reporter.info("Failed :(, but I learned: "+ces.map(_.mkString(",")).mkString("  |  "))
              testBank ++= ces.map(InExample(_))
            }
          } else {
            reporter.info("ZZUCCESS!")
          }
        }


        if (solutions.isEmpty) {
            reporter.info("Trey aagggain")
            repair()
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
  }

  discoverTests()
}
