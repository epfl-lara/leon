/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import leon._
import leon.purescala.Definitions.Program
import leon.LeonContext
import leon.utils._
import leon.frontends.scalac.ExtractionPhase

import org.scalatest._
import org.scalatest.exceptions.TestFailedException

trait LeonTestSuite extends fixture.FunSuite {
  type FixtureParam = LeonContext

  override def withFixture(test: OneArgTest): Outcome = {
    val reporter = new TestSilentReporter
    val opts     = List[String]()

    val ctx      = Main.processOptions(opts).copy(reporter = reporter)

    try {
      test(ctx)
    } catch {
      case fe: LeonFatalError =>
        reporter.lastErrors ++= fe.msg
        Failed(new TestFailedException(reporter.lastErrors.mkString("\n"), fe, 5))
    }
  }

  def parseString(str: String)(implicit ctx: LeonContext): Program = {
    parseStrings(List(str))(ctx)
  }

  def parseStrings(strs: List[String])(implicit ctx: LeonContext): Program = {
    val pipeline = TemporaryInputPhase andThen
                   ExtractionPhase andThen
                   PreprocessingPhase

    val errorsBefore = ctx.reporter.errorCount

    val program = pipeline.run(ctx)((strs, Nil))

    assert(ctx.reporter.errorCount === errorsBefore)

    program
  }

}
