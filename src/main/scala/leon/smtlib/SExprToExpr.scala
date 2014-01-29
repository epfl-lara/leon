package leon
package smtlib

import purescala._
import Common._
import Trees._
import Extractors._
import TreeOps._
import TypeTrees._
import Definitions._

import _root_.smtlib.sexpr
import sexpr.SExprs._
import _root_.smtlib.Commands.{Identifier => SmtLibIdentifier, _}

object SExprToExpr {

  def apply(sexpr: SExpr, context: Map[String, Expr], constructors: Map[String, CaseClassDef]): Expr = sexpr match {
    case SInt(n) => IntLiteral(n.toInt)
    case SSymbol("TRUE") => BooleanLiteral(true)
    case SSymbol("FALSE") => BooleanLiteral(false)
    case SSymbol(s) => constructors.get(s) match {
      case Some(app) => CaseClass(app, Seq())
      case None => context(s)
    }
    case SList(SSymbol(app) :: args) if(constructors.isDefinedAt(app)) => 
      CaseClass(constructors(app), args.map(apply(_, context, constructors)))

    case SList(List(SSymbol("LET"), SList(defs), body)) => {
      val leonDefs: Seq[(Identifier, Expr, String)] = defs.map {
        case SList(List(SSymbol(sym), value)) => (FreshIdentifier(sym), apply(value, context, constructors), sym)
      }
      val recBody = apply(body, context ++ leonDefs.map(p => (p._3, p._1.toVariable)), constructors)
      leonDefs.foldRight(recBody)((binding, b) => Let(binding._1, binding._2, b))
    }
    case SList(SSymbol(app) :: args) => {
      val recArgs = args.map(arg => apply(arg, context, constructors))
      app match {
        case "-" => recArgs match {
          case List(a) => UMinus(a)
          case List(a, b) => Minus(a, b)
        }
      }
    }
    case o => sys.error("TODO converting from s-expr: " + o)
  }

}
