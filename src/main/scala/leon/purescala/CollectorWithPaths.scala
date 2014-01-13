package leon
package purescala

import Trees._
import TreeOps._
import Definitions._

trait CollectorWithPaths[T] extends TransformerWithPC with Traverser[Seq[T]] {
  type C = Seq[Expr]
  val initC : C = Nil
  def register(e: Expr, path: C) = path :+ e

  private var results: Seq[T] = Nil

  def collect(e: Expr, path: Seq[Expr]): Option[T]

  def walk(e: Expr, path: Seq[Expr]): Option[Expr] = None

  override final def rec(e: Expr, path: Seq[Expr]) = {
    collect(e, path).foreach { results :+= _ }
    walk(e, path) match {
      case Some(r) => r
      case _ => super.rec(e, path)
    }
  }

  def traverse(funDef: FunDef): Seq[T] = {
    import HOTreeOps._
    val precondition = funDef.precondition.map(e => killForallExpressions(matchToIfThenElse(e))).toSeq
    val precTs = funDef.precondition.map(e => traverse(preProcess(e))).toSeq.flatten
    val bodyTs = funDef.body.map(e => traverse(preProcess(e), precondition)).toSeq.flatten
    val postTs = funDef.postcondition.map(p => traverse(preProcess(p._2))).toSeq.flatten
    precTs ++ bodyTs ++ postTs
  }

  def traverse(e: Expr): Seq[T] = traverse(e, initC)

  def traverse(e: Expr, init: Expr): Seq[T] = traverse(e, Seq(init))

  def traverse(e: Expr, init: Seq[Expr]): Seq[T] = {
    results = Nil
    rec(e, init)
    results
  }
}

// vim: set ts=4 sw=4 et:
