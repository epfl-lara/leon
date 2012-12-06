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


  def testFile(file: String): (((Solver, FunDef, Problem) => Unit) => Unit) = testFile{
    val res = this.getClass.getClassLoader.getResource(file)

    if(res == null || res.getProtocol != "file") {
      assert(false, "Tests have to be run from within `sbt`, for otherwise " +
                    "the test files will be harder to access (and we dislike that).")
    }

    new File(res.toURI)
  }

  def testFile(file: File)(block: (Solver, FunDef, Problem) => Unit) {
    val fullName = file.getPath()
    val start = fullName.indexOf("synthesis")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    assert(file.exists && file.isFile && file.canRead,
           "Benchmark [%s] is not a readable file".format(displayName))


    val ctx = LeonContext(
      settings = Settings(
        synthesis = true,
        xlang     = false,
        verify    = false
      ),
      files = List(file),
      reporter = new SilentReporter
    )

    val opts = SynthesizerOptions()

    val pipeline = leon.plugin.ExtractionPhase andThen ExtractProblemsPhase

    val (results, solver) = pipeline.run(ctx)(file.getPath :: Nil)

    for ((f, ps) <- results; p <- ps) {
      test("Synthesizing %3d: %-20s [%s]".format(nextInt(), f.id.toString, displayName)) {
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


  testFile("synthesis/Cegis1.scala") {
    case (solver, fd, p) => 
      val sctx = SynthesisContext(solver, new SilentReporter, new java.util.concurrent.atomic.AtomicBoolean)

      assertRuleSuccess(sctx, rules.CEGIS.instantiateOn(sctx, p))
      assertFastEnough(sctx, rules.CEGIS.instantiateOn(sctx, p), 100)
  }
}
