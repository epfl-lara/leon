/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import leon._
import leon.purescala.Definitions.Program
import leon.utils._
import leon.frontends.scalac.ExtractionPhase

import org.scalatest._
import org.scalatest.exceptions.TestFailedException

import scala.language.implicitConversions

trait LeonTestSuiteWithProgram extends fixture.FunSuite {

  implicit def fixtureToCtx(implicit f: FixtureParam): LeonContext = f._1
  implicit def fixtureToPgm(implicit f: FixtureParam): Program = f._2

  val leonOpts = List[String]()

  val pipeline =
    TemporaryInputPhase andThen
    ExtractionPhase andThen
    new PreprocessingPhase

  val sources: List[String]

  private[this] var fixtureCache: Option[(LeonContext, Program)] = None

  def getFixture(): (LeonContext, Program) = synchronized {
    if (fixtureCache.isEmpty) {
      val reporter = new TestSilentReporter
      val im       = new InterruptManager(reporter)

      val ctx      = Main.processOptions(leonOpts).copy(reporter = reporter, interruptManager = im)

      val pgm      = pipeline.run(ctx)((sources, Nil))

      fixtureCache = Some((ctx, pgm))
    }

    fixtureCache.get
  }

  type FixtureParam = (LeonContext, Program)

  override def withFixture(test: OneArgTest): Outcome = {
    try {
      val (ctx, pgm) = getFixture()
      try {
        val freshReporter = new TestSilentReporter

        val f = (ctx.copy(reporter = freshReporter), pgm)

        test(f)
      } catch {
        case fe: LeonFatalError =>
          ctx.reporter match {
            case sr: TestSilentReporter =>
              sr.lastErrors ++= fe.msg
              Failed(new TestFailedException(sr.lastErrors.mkString("\n"), fe, 5))
          }
      }
    } catch {
      case t: Throwable  =>
        Failed(t)
    }
  }
}

