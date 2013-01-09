package leon.test.synthesis

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}

class SynthesisSuite extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  def forProgram(title: String)(content: String)(block: (SynthesisContext, FunDef, Problem) => Unit) {

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

    val pipeline = leon.plugin.TemporaryInputPhase andThen leon.plugin.ExtractionPhase andThen SynthesisProblemExtractionPhase

    val (program, results) = pipeline.run(ctx)((content, Nil))

    val solver = new FairZ3Solver(ctx)
    solver.setProgram(program)

    for ((f, ps) <- results; p <- ps) {
      test("Synthesizing %3d: %-20s [%s]".format(nextInt(), f.id.toString, title)) {
        val sctx = SynthesisContext(ctx, opts, Some(f), program, solver, new DefaultReporter, new java.util.concurrent.atomic.AtomicBoolean)

        block(sctx, f, p)
      }
    }
  }

  def assertAllAlternativesSucceed(sctx: SynthesisContext, rr: Traversable[RuleInstantiation]) {
    assert(!rr.isEmpty)

    for (r <- rr) {
      assertRuleSuccess(sctx, r)
    }
  }

  def assertRuleSuccess(sctx: SynthesisContext, rr: RuleInstantiation): Option[Solution] = {
    rr.apply(sctx) match {
      case RuleSuccess(sol) =>
        Some(sol)
      case _ =>
        assert(false, "Rule did not succeed")
        None
    }
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
    case (sctx, fd, p) =>
      assertAllAlternativesSucceed(sctx, rules.CEGIS.instantiateOn(sctx, p))
      assertFastEnough(sctx, rules.CEGIS.instantiateOn(sctx, p), 100)
  }

  forProgram("Cegis 2")(
    """
import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object Injection {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // simulates input/output spec.
  def tail(in: List) = choose {
    (out: List) =>
      (in != Cons(0, Nil())                   || out == Nil()) &&
      (in != Cons(0, Cons(1, Nil()))          || out == Cons(1, Nil())) &&
      (in != Cons(0, Cons(1, Cons(2, Nil()))) || out == Cons(1, Cons(2, Nil())))
  }
}
    """
  ) {
    case (sctx, fd, p) =>
      rules.CEGIS.instantiateOn(sctx, p).head.apply(sctx) match {
        case RuleSuccess(sol) =>
          assert(false, "CEGIS should have failed, but found : %s".format(sol))
        case _ =>
      }

      rules.ADTSplit.instantiateOn(sctx, p).head.apply(sctx) match {
        case RuleDecomposed(subs) =>
          for (sub <- subs; alt <- rules.CEGIS.instantiateOn(sctx, sub)) {
            assertRuleSuccess(sctx, alt)
          }
        case _ =>
          assert(false, "Woot?")
      }
  }
}
