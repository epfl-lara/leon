/* Copyright 2009-2016 EPFL, Lausanne */

package leon.test

import leon._

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
}
