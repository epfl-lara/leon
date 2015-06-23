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
import testcases._

class LeonAllTests extends Suites(
  new LeonUnitTests,
  new LeonFunTests,
  new TestCasesCompile
)

class LeonFunTests extends Suites(
  new FrontEndsSuite,

  new RepairSuite,

  new TerminationSuite,

  new StablePrintingSuite,
  new SynthesisSuite,
  new SynthesisRegressionSuite,

  new LibraryVerificationSuite,
  new PureScalaVerificationSuite,
  new XLangVerificationSuite
)

class LeonUnitTests extends Suites(
  new CodeGenSuite,

  new ImportsSuite,

  new StreamsSuite,

  new DefOpsSuite,
  new LikelyEqSuite,
  new TransformationSuite,
  new TreeNormalizationsSuite,
  new TreeOpsSuite,
  new TreeTestsSuite,

  new EnumerationSolverSuite,
  new TimeoutSolverSuite,
  new UnrollingSolverSuite,

  new AlgebraSuite,
  new LinearEquationsSuite,

  new DefaultEvaluatorSuite,
  new EvaluatorSuite
)
