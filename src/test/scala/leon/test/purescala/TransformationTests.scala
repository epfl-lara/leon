/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.purescala

import leon._
import leon.test._
import leon.utils.{TemporaryInputPhase, PreprocessingPhase}
import leon.frontends.scalac.ExtractionPhase

import leon.purescala.ScalaPrinter
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers.z3.UninterpretedZ3Solver
import leon.solvers._

class TransformationTests extends LeonTestSuite {

  val pipeline = ExtractionPhase andThen PreprocessingPhase
 
  val simpPaths = (p: Program, e : Expr) => {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(testContext, p))
    simplifyPaths(uninterpretedZ3)(e)
  }

  filesInResourceDir("regression/transformations").foreach { file =>
    // Configure which file corresponds to which transformation:

    val (title: String, transformer: ((Program,Expr) => Expr)) = file.getName match {
      case "SimplifyLets.scala" =>
        (
          "Simplifying Lets",
          (_:Program, e : Expr) => simplifyLets(e)
        )
      case "SimplifyPaths.scala" =>
        (
          "Simplifying paths",
          simpPaths
        )
      case n =>
        fail("Unknown name "+n)
    }

    test(title) {
      val ctx = testContext.copy(
        files   = List(file)
      )

      val prog = pipeline.run(ctx)(file.getPath :: Nil)

      // Proceed with the actual tests
      val inputs = prog.definedFunctions.collect{
        case fd if fd.id.name.startsWith("input") =>
          (fd.id.name.substring(5,7), fd)
      }.toSeq.sortBy(_._1)

      val outputs = prog.definedFunctions.collect{
        case fd if fd.id.name.startsWith("output") =>
          (fd.id.name.substring(6,8), fd)
      }.toMap

      for ((n, fdin) <- inputs) {
        info(title +" ["+n+"]")
        val in = fdin.body.get
        outputs.get(n) match {
          case Some(fdexp) =>
            val out = transformer(prog, in)
            val exp = fdexp.body.get

            val map = (fdin.params.map(_.id) zip fdexp.params.map(_.id)).toMap

            if (!isHomomorphic(out, exp)(map)) {
              fail("Produced tree does not match\nGot:\n"+out+"\nExpected:\n"+exp+"\n")
            }

          case None =>
            fail("No output for "+n+" ?!?")
        }
      }
    }
  }

  def apply(trs: Expr => Expr *): Expr => Expr = {
    { (e: Expr) => trs.foldLeft(e){ (x, tr) => tr(x) } }
  }
}

