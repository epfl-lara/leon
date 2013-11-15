/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package purescala

import leon._
import leon.plugin.{TemporaryInputPhase,ExtractionPhase}

import leon.purescala.ScalaPrinter
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

class TransformationTests extends LeonTestSuite {

  val pipeline = leon.plugin.ExtractionPhase andThen leon.utils.SubtypingPhase

  filesInResourceDir("regression/transformations").foreach { file =>
    val ctx = testContext.copy(
      files   = List(file)
    )

    val prog = pipeline.run(ctx)(file.getPath :: Nil)

    // Configure which file corresponds to which transformation:

    val (title: String, transformer: (Expr => Expr)) = file.getName match {
      case "SimplifyLets.scala" =>
        (
          "Simplifying Lets",
          simplifyLets _
        )
      case "Match.scala" =>
        (
          "Match reconstruction/flattening",
          apply (matchToIfThenElse _, patternMatchReconstruction _)
        )
      case n =>
        fail("Unknown name "+n)
    }


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
      test(title +" ["+n+"]") {
        val in = fdin.body.get
        outputs.get(n) match {
          case Some(fdexp) =>
            val out = transformer(in)
            val exp = fdexp.body.get

            val map = (fdin.args.map(_.id) zip fdexp.args.map(_.id)).toMap

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

