/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import org.scalatest.Suites
import evaluators._
import codegen._
import frontends._
import purescala._
import solvers._
import repair._
import synthesis._
import termination._
import utils._
import verification._

class LeonAllTests extends Suites(
  new LeonUnitTests,
  new LeonFunTests
)

class LeonFunTests extends Suites(
  new FrontEndsTest,

  new RepairSuite,

  new TerminationRegression,

  new StablePrintingSuite,
  new SynthesisSuite,
  new SynthesisRegressionSuite,


  new LibraryVerificationRegression,
  new PureScalaVerificationRegression,
  new XLangVerificationRegression,

  new TestCasesCompile
)

class LeonUnitTests extends Suites(
  new CodeGenTests,

  new ImportsTests,

  new Streams,

  new DefOpsTests,
  new LikelyEqSuite,
  new TransformationTests,
  new TreeNormalizationsTests,
  new TreeOpsTests,
  new TreeTests,

  new EnumerationSolverTests,
  new TimeoutSolverTests,
  new UnrollingSolverTests,

  new AlgebraSuite,
  new LinearEquationsSuite,

  new DefaultEvaluatorTests,
  new EvaluatorsTests
)
