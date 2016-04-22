/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package xlang

import purescala.Expressions._
import xlang.Expressions._
import purescala.ExprOps._
import purescala.Common._

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
        val filtered = exprs.filter{
          case UnitLiteral() => false
          case _ => true
        }
        val nexprs = (filtered :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
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

  def rewriteIDs(substs: Map[Identifier, Identifier], expr: Expr) : Expr = {
    postMap({
      case Assignment(i, v) => substs.get(i).map(ni => Assignment(ni, v))
      case FieldAssignment(o, i, v) => substs.get(i).map(ni => FieldAssignment(o, ni, v))
      case Variable(i) => substs.get(i).map(ni => Variable(ni))
      case _ => None
    })(expr)
  }
}

