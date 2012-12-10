package leon.test.synthesis

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}

object ExtractProblemsPhase extends LeonPhase[Program, (Map[FunDef, Seq[Problem]], Solver)] {
  val name        = "Synthesis Problem Extraction"
  val description = "Synthesis Problem Extraction"

  def run(ctx: LeonContext)(p: Program): (Map[FunDef, Seq[Problem]], Solver) = {

     val silentContext : LeonContext = ctx.copy(reporter = new SilentReporter)
     val mainSolver = new FairZ3Solver(silentContext)
     mainSolver.setProgram(p)

    var results  = Map[FunDef, Seq[Problem]]()
    def noop(u:Expr, u2: Expr) = u


    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case ch @ Choose(vars, pred) =>
        val problem = Problem.fromChoose(ch)

        results += f -> (results.getOrElse(f, Seq()) :+ problem)

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- p.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
    }

    (results, mainSolver)
  }

}

class SynthesisSuite extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  def forProgram(title: String)(content: String)(block: (Solver, FunDef, Problem) => Unit) {

    val ctx = LeonContext(
      settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false
      ),
      files = List(),
      reporter = new SilentReporter
    )

    val opts = SynthesizerOptions()

    val pipeline = leon.plugin.TemporaryInputPhase andThen leon.plugin.ExtractionPhase andThen ExtractProblemsPhase

    val (results, solver) = pipeline.run(ctx)((content, Nil))

    for ((f, ps) <- results; p <- ps) {
      test("Synthesizing %3d: %-20s [%s]".format(nextInt(), f.id.toString, title)) {
        block(solver, f, p)
      }
    }
  }

  def assertRuleSuccess(sctx: SynthesisContext, rr: Traversable[RuleInstantiation]) {
    assert(rr.isEmpty === false, "No rule alternative while the rule should have succeeded")
    assert(rr.exists(alt => alt.apply(sctx).isInstanceOf[RuleSuccess]) === true, "Rule did not succeed")
  }


  def assertFastEnough(sctx: SynthesisContext, rr: Traversable[RuleInstantiation], timeoutMs: Long) {
    for (alt <- rr) {
      val ts = System.currentTimeMillis

      val res = alt.apply(sctx)

      val t = System.currentTimeMillis - ts

      t should be <= timeoutMs
    }
  }


  forProgram("Cegis 1")(
    """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object Injection {
  sealed abstract class List
  case class Cons(tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def simple(in: List) = choose{out: List => size(out) == size(in) }
}
    """
  ) {
    case (solver, fd, p) =>
      val sctx = SynthesisContext(solver, new SilentReporter, new java.util.concurrent.atomic.AtomicBoolean)

      assertRuleSuccess(sctx, rules.CEGIS.instantiateOn(sctx, p))
      assertFastEnough(sctx, rules.CEGIS.instantiateOn(sctx, p), 100)
  }
}
