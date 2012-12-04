package leon.test.synthesis

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.synthesis._

import org.scalatest.FunSuite

import java.io.{BufferedWriter, FileWriter, File}

class SynthesisTestPhase(val options: SynthesizerOptions, 
                         val rules: Set[Rule]) extends LeonPhase[Program, Map[Choose, (Solution, Boolean)]] {
  val name        = "Synthesis-test"
  val description = "Synthesis-test"

  def run(ctx: LeonContext)(p: Program): Map[Choose, (Solution, Boolean)] = {
    val silentContext : LeonContext = ctx.copy(reporter = new SilentReporter)

    val mainSolver = new FairZ3Solver(silentContext)
    mainSolver.setProgram(p)

    val uninterpretedZ3 = new UninterpretedZ3Solver(silentContext)
    uninterpretedZ3.setProgram(p)

    def synthesizeAll(program: Program): Map[Choose, (Solution, Boolean)] = {
      def noop(u:Expr, u2: Expr) = u

      var solutions = Map[Choose, (Solution, Boolean)]()

      def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
        case ch @ Choose(vars, pred) =>
          val problem = Problem.fromChoose(ch)
          val synth = new Synthesizer(ctx,
                                      mainSolver,
                                      p,
                                      problem,
                                      rules,
                                      options)
          val (sol, isComplete) = synth.synthesize()

          solutions += ch -> (sol, isComplete)

          a
        case _ =>
          a
      }

      // Look for choose()
      for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
        if (options.filterFuns.isEmpty || options.filterFuns.get.contains(f.id.toString)) {
          treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
        }
      }

      solutions
    }

    synthesizeAll(p)
  }
}

class SynthesisRuleTestPhase(val options: SynthesizerOptions, 
                             val rule: Rule) extends LeonPhase[Program, Map[Choose, RuleResult]] {
  val name        = "Synthesis-test"
  val description = "Synthesis-test"

  def run(ctx: LeonContext)(p: Program): Map[Choose, RuleResult] = {

    val silentContext : LeonContext = ctx.copy(reporter = new SilentReporter)
    val mainSolver = new FairZ3Solver(silentContext)
    mainSolver.setProgram(p)

    def synthesizeAll(program: Program): Map[Choose, RuleResult] = {
      def noop(u:Expr, u2: Expr) = u

      var results = Map[Choose, RuleResult]()


      def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
        case ch @ Choose(vars, pred) =>
          val problem = Problem.fromChoose(ch)

          val sctx = SynthesisContext(mainSolver, silentContext.reporter)

          results += ch -> rule.attemptToApplyOn(sctx, problem)

          a
        case _ =>
          a
      }

      // Look for choose()
      for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
        if (options.filterFuns.isEmpty || options.filterFuns.get.contains(f.id.toString)) {
          treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
        }
      }

      results
    }

    synthesizeAll(p)
  }
}

class SynthesisSuite extends FunSuite {
  private var counter : Int = 0
  private def nextInt() : Int = {
    counter += 1
    counter
  }

  def synthesisSearch(file: File, rules: Set[Rule])(block: Map[Choose, (Solution, Boolean)] => Unit) {
    val fullName = file.getPath()
    val start = fullName.indexOf("synthesis")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("Synthesizing %3d: [%s]".format(nextInt(), displayName)) {
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

      val pipeline = leon.plugin.ExtractionPhase andThen new SynthesisTestPhase(opts, rules)

      block(pipeline.run(ctx)("--synthesize" :: file.getPath :: Nil))
    }
  }

  def synthesisStep(file: File, rule: Rule)(block: Map[Choose, RuleResult] => Unit) {
    val fullName = file.getPath()
    val start = fullName.indexOf("synthesis")

    val displayName = if(start != -1) {
      fullName.substring(start, fullName.length)
    } else {
      fullName
    }

    test("Synthesizing %3d: [%s]".format(nextInt(), displayName)) {
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

      val pipeline = leon.plugin.ExtractionPhase andThen new SynthesisRuleTestPhase(opts, rule)

      block(pipeline.run(ctx)("--synthesize" :: file.getPath :: Nil))
    }
  }

  def assertInnaplicable(rr: RuleResult) {
    assert(rr.alternatives.forall(alt => alt.apply() == RuleApplicationImpossible) === true, "Rule was applicable")
  }

  def assertSuccess(rr: RuleResult) {
    assert(rr.alternatives.isEmpty === false, "No rule alternative while the rule should have succeeded")
    assert(rr.alternatives.exists(alt => alt.apply().isInstanceOf[RuleSuccess]) === true, "Rule did not succeed")
  }

  def fileFor(name: String): File = {
    val res = this.getClass.getClassLoader.getResource(name)

    if(res == null || res.getProtocol != "file") {
      assert(false, "Tests have to be run from within `sbt`, for otherwise " +
                    "the test files will be harder to access (and we dislike that).")
    }

    new File(res.toURI)
  }

  synthesisStep(fileFor("synthesis/Cegis1.scala"), rules.CEGIS) { res => 
    for ((ch, rr) <- res) {
      assertSuccess(rr)
    }
  }
}
