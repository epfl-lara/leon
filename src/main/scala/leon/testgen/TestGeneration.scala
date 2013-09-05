/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package testgen

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.xlang.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.ScalaPrinter
import leon.Reporter

import leon.solvers._
import leon.solvers.z3._

import scala.collection.mutable.{Set => MutableSet}

// TODO FIXME if this class is to be resurrected, make it a proper LeonPhase.
@deprecated("Unused, Untested, Unmaintained.", "")
class TestGeneration(context : LeonContext) { 

  def description: String = "Generate random testcases"
  def shortDescription: String = "test"

  private val reporter = context.reporter

  def analyse(program: Program) {
    val z3Solver = new FairZ3SolverFactory(context, program)
    reporter.info("Running test generation")

    val testcases = generateTestCases(program)

    val topFunDef = program.definedFunctions.find(fd => isMain(fd)).get

    val testFun = new FunDef(FreshIdentifier("test"), UnitType, Seq())
    val funInvocs = testcases.map(testcase => {
      val params = topFunDef.args
      val args = topFunDef.args.map{
        case VarDecl(id, tpe) => testcase.get(id) match {
          case Some(v) => v
          case None => simplestValue(tpe)
        }
      }
      FunctionInvocation(topFunDef, args)
    }).toSeq
    testFun.body = Some(Block(funInvocs, UnitLiteral))

    val Program(id, ObjectDef(objId, defs, invariants)) = program
    val testProgram = Program(id, ObjectDef(objId, testFun +: defs , invariants))
    testProgram.writeScalaFile("TestGen.scalax")

    reporter.info("Running from waypoint with the following testcases:\n")
    reporter.info(testcases.mkString("\n"))
  }

  private def isMain(fd: FunDef): Boolean = {
    fd.annotations.exists(_ == "main")
  }

  def generatePathConditions(program: Program): Set[Expr] = {
    val z3Solver = new FairZ3SolverFactory(context, program)

    val callGraph = new CallGraph(program)
    callGraph.writeDotFile("testgen.dot")
    val constraints = callGraph.findAllPaths(z3Solver).map(path => {
      println("Path is: " + path)
      val cnstr = callGraph.pathConstraint(path)
      println("constraint is: " + cnstr)
      cnstr
    })
    constraints
  }

  private def generateTestCases(program: Program): Set[Map[Identifier, Expr]] = {
    val allPaths = generatePathConditions(program)
    val z3Solver = new FairZ3SolverFactory(context, program)

    allPaths.flatMap(pathCond => {
      reporter.info("Now considering path condition: " + pathCond)

      var testcase: Option[Map[Identifier, Expr]] = None
        
      z3Solver.restartZ3
      val (solverResult, model) = SimpleSolverAPI(z3Solver).solveSAT(pathCond)

      solverResult match {
        case None => Seq()
        case Some(false) => {
          reporter.info("The path is unreachable")
          Seq()
        }
        case Some(true) => {
          reporter.info("The model should be used as the testcase")
          Seq(model)
        }
      }
    })
  }
}



