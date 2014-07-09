/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees.BooleanType

abstract class Tactic(vctx: VerificationContext) {
  val description : String
  val shortDescription : String

  val program  = vctx.program
  val reporter = vctx.reporter

  def generateVCs(fd: FunDef): Seq[VerificationCondition] = {
    generatePostconditions(fd) ++
    generatePreconditions(fd) ++
    generateCorrectnessConditions(fd)
  }

  def generatePostconditions(function: FunDef): Seq[VerificationCondition]
  def generatePreconditions(function: FunDef): Seq[VerificationCondition]
  def generateCorrectnessConditions(function: FunDef): Seq[VerificationCondition]


  // Helper functions
  protected def safe(e: Expr): Expr = matchToIfThenElse(e)
  protected def precOrTrue(fd: FunDef): Expr = fd.precondition match {
    case Some(pre) => safe(pre)
    case None => BooleanLiteral(true)
  }

  protected def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Expr)] = {
    CollectorWithPaths(f).traverse(expr)
  }

  protected def breakConjunct(e : Expr) : Seq[Expr] = e match {
    case And(exs) => exs
    case Let(id,body,cond) if cond.getType == BooleanType =>
      for (fragment <- breakConjunct(cond)) yield Let(id, body, fragment).setPos(fragment)
    case _ => Seq(e)
  }

  def breakIfNeeded(e : Expr) = if (vctx.fineGrain) breakConjunct(e) else Seq(e)
}
