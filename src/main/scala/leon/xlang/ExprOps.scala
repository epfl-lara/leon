/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package xlang

import purescala.Expressions._
import xlang.Expressions._
import purescala.ExprOps._

object ExprOps {
  
  def isXLang(expr: Expr): Boolean = exists {
    _.isInstanceOf[XLangExpr]
  }(expr)

  def containsEpsilon(e: Expr) = exists{
    case _ : Epsilon => true
    case _ => false
  }(e)

  def flattenBlocks(expr: Expr): Expr = {
    postMap({
      case Block(exprs, last) =>
        val nexprs = (exprs :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
          case UnitLiteral() => Seq()
          case e2 => Seq(e2)
        }
        Some(nexprs match {
          case Seq() => UnitLiteral()
          case Seq(e) => e
          case es => Block(es.init, es.last)
        })
      case _ =>
        None
    })(expr)
  }
}

