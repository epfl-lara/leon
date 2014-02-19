/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Trees._
import xlang.Trees._
import purescala.TreeOps._
import purescala.Extractors._

object TreeOps {

  //checking whether the expr is not pure, that is it contains any non-pure construct: 
  // assign, while, blocks, array, ...
  def isXLang(expr: Expr): Boolean = {
    exists { _ match {
      case Block(_, _) => true
      case Assignment(_, _) => true
      case While(_, _) => true
      case LetVar(_, _, _) => true
      case LetDef(_, _) => true
      case ArrayUpdate(_, _, _) => true
      case ArrayMake(_) => true
      case ArrayClone(_) => true
      case Epsilon(_) => true
      case _ => false
    }}(expr)
  }

  def containsEpsilon(e: Expr) = exists{ _ match {
      case (l: Epsilon) => true
      case _ => false
  }}(e)

  def flattenBlocks(expr: Expr): Expr = {
    postMap({
      case Block(exprs, last) =>
        val nexprs = (exprs :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
          case UnitLiteral => Seq()
          case e2 => Seq(e2)
        }
        Some(nexprs match {
          case Seq() => UnitLiteral
          case Seq(e) => e
          case es => Block(es.init, es.last).setType(es.last.getType)
        })
      case _ =>
        None
    })(expr)
  }
}
