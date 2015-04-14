/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import purescala.Expressions._
import xlang.Expressions._
import purescala.ExprOps._

object ExprOps {
  
  def isXLang(expr: Expr): Boolean = exists {
    case Block(_, _) | Assignment(_, _) |
         While(_, _) | Epsilon(_, _) |
         EpsilonVariable(_, _) |
         LetVar(_, _, _) | Waypoint(_, _, _) |
         ArrayUpdate(_, _, _) 
       => true
    case _ => false
  }(expr)

  def containsEpsilon(e: Expr) = exists{
    case (l: Epsilon) => true
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

