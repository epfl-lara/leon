/* Copyright 2009-2013 EPFL, Lausanne */

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

    val opts = SynthesisOptions()

    val pipeline = leon.plugin.TemporaryInputPhase andThen leon.plugin.ExtractionPhase andThen SynthesisProblemExtractionPhase

    val (program, results) = pipeline.run(ctx)((content, Nil))

    val solver = new FairZ3Solver(ctx)
    solver.setProgram(program)

    val simpleSolver = new UninterpretedZ3Solver(ctx)
    simpleSolver.setProgram(program)

    for ((f, ps) <- results; p <- ps) {
      test("Synthesizing %3d: %-20s [%s]".format(nextInt(), f.id.toString, title)) {
        val sctx = SynthesisContext(ctx,
                                    opts,
                                    Some(f),
                                    program,
                                    solver,
                                    simpleSolver,
                                    new DefaultReporter,
                                    new java.util.concurrent.atomic.AtomicBoolean)

        block(sctx, f, p)
      }
    }
  }

  case class Apply(desc: String, andThen: List[Apply] = Nil)

  def synthesizeWith(sctx: SynthesisContext, p: Problem, ss: Apply): Solution = {
    val (normRules, otherRules) = sctx.options.rules.partition(_.isInstanceOf[NormalizingRule])
    val normApplications = normRules.flatMap(_.instantiateOn(sctx, p))

    val apps = if (!normApplications.isEmpty) {
      normApplications
    } else {
      otherRules.flatMap { r => r.instantiateOn(sctx, p) }
    }

    def matchingDesc(app: RuleInstantiation, ss: Apply): Boolean = {
      import java.util.regex.Pattern;
      val pattern = Pattern.quote(ss.desc).replace("*", "\\E.*\\Q")
      app.toString.matches(pattern)
    }

    apps.filter(matchingDesc(_, ss)) match {
      case app :: Nil =>
        app.apply(sctx) match {
          case RuleSuccess(sol, trusted) =>
            assert(ss.andThen.isEmpty)
            sol

          case RuleDecomposed(sub) =>
            val subSols = (sub zip ss.andThen) map { case (p, ss) => synthesizeWith(sctx, p, ss) }
            app.onSuccess(subSols).get

          case _ =>
            throw new AssertionError("Failed to apply "+app+" on "+p)
        }

      case Nil =>
        throw new AssertionError("Failed to find "+ss.desc+". Available: "+apps.mkString(", "))

      case xs =>
        throw new AssertionError("Ambiguous "+ss.desc+". Found: "+xs.mkString(", "))
    }
  }

  def synthesize(title: String)(program: String)(strategies: PartialFunction[String, Apply]) {
    forProgram(title)(program) {
      case (sctx, fd, p) =>
        strategies.lift.apply(fd.id.toString) match {
          case Some(ss) =>
            synthesizeWith(sctx, p, ss)

          case None =>
            assert(false, "Function "+fd.id.toString+" not found")
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
      case RuleSuccess(sol, trusted) =>
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
        case RuleSuccess(sol, trusted) =>
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


  synthesize("Lists")("""
import leon.Utils._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  def concat(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }

  def insert(in1: List, v: Int) = choose {
    (out : List) =>
      content(out) == content(in1) ++ Set(v)
  }

  def insertSorted(in1: List, v: Int) = choose {
    (out : List) =>
      isSorted(in1) && content(out) == content(in1) ++ Set(v) && isSorted(out)
  }
}
    """) {
    case "concat" =>
      Apply("ADT Induction on 'in1'", List(
        Apply("CEGIS"),
        Apply("CEGIS")
      ))

    case "insert" =>
      Apply("ADT Induction on 'in1'", List(
        Apply("CEGIS"),
        Apply("CEGIS")
      ))

    case "insertSorted" =>
      Apply("Assert isSorted(in1)", List(
        Apply("ADT Induction on 'in1'", List(
          Apply("Ineq. Split on 'head*' and 'v*'", List(
            Apply("CEGIS"),
            Apply("CEGIS"),
            Apply("CEGIS")
          )),
          Apply("CEGIS")
        ))
      ))
  }
}
