/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package invariant.templateSolvers

import z3.scala._
import leon.solvers._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import leon.LeonContext
import leon.solvers.z3.UninterpretedZ3Solver

/**
 *  A uninterpreted solver extended with additional functionalities.
 *  TODO: need to handle bit vectors
 */
class ExtendedUFSolver(context : LeonContext, program: Program)
  extends UninterpretedZ3Solver(context, program) {

  override val name = "Z3-eu"
  override val description = "Extended UF-ADT Z3 Solver"

  /**
   * This uses z3 methods to evaluate the model
   */
  def evalExpr(expr: Expr): Option[Expr] = {
    val ast = toZ3Formula(expr)
    val model = solver.getModel
    val res = model.eval(ast, true)
    if (res.isDefined)
      Some(fromZ3Formula(model, res.get, null))
    else None
  }

  def getAssertions : Expr = {
    val assers = solver.getAssertions.map((ast) => fromZ3Formula(null, ast, null))
    And(assers)
  }

  /**
   * Uses z3 to convert a formula to SMTLIB.
   */
  def ctrsToString(logic: String, unsatcore: Boolean = false): String = {
    z3.setAstPrintMode(Z3Context.AstPrintMode.Z3_PRINT_SMTLIB2_COMPLIANT)
    var seenHeaders = Set[String]()
    var headers = Seq[String]()
    var asserts = Seq[String]()
    solver.getAssertions().toSeq.foreach((asser) => {
      val str = z3.benchmarkToSMTLIBString("benchmark", logic, "unknown", "", Seq(), asser)
      //remove from the string the headers and also redeclaration of template variables
      //split based on newline to get a list of strings
      val strs = str.split("\n")
      val newstrs = strs.filter((line) => !seenHeaders.contains(line))
      var newHeaders = Seq[String]()
      newstrs.foreach((line) => {
        if (line == "; benchmark") newHeaders :+= line
        else if (line.startsWith("(set")) newHeaders :+= line
        else if (line.startsWith("(declare")) newHeaders :+= line
        else if(line.startsWith("(check-sat)")) {} //do nothing
        else asserts :+= line
      })
      headers ++= newHeaders
      seenHeaders ++= newHeaders
    })
    val initstr = if (unsatcore) {
      "(set-option :produce-unsat-cores true)"
    } else ""
    val smtstr = headers.foldLeft(initstr)((acc, hdr) => acc + "\n" + hdr) + "\n" +
      asserts.foldLeft("")((acc, asrt) => acc + "\n" + asrt) + "\n" +
      "(check-sat)" + "\n" +
      (if (!unsatcore) "(get-model)"
      else "(get-unsat-core)")
    smtstr
  }
}
