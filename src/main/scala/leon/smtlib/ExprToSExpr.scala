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

/** This pretty-printer prints an SMTLIB2 representation of the Purescala program */
object ExprToSExpr {

  //returns the set of free identifier
  def apply(tree: Expr): (SExpr, Set[Identifier]) = {

    var freeVars: Set[Identifier] = Set()
    
    def rec(t: Expr): SExpr = t match {
      case Variable(id) => {
        val sym = id2sym(id)
        freeVars += id
        sym
      }
      //case LetTuple(ids,d,e) => SList(List(
      //  SSymbol("let"),
      //  SList(List(ids))
      case Let(b,d,e) => {
        val id = id2sym(b)
        val value = rec(d)
        val newBody = rec(e)
        freeVars -= b
        
        SList(
          SSymbol("let"),
          SList(
            SList(id, value)
          ),
          newBody
        )
      }

      case er@Error(_) => {
        val id = FreshIdentifier("error_value").setType(er.getType)
        val sym = id2sym(id)
        freeVars += id
        sym
      }

      case And(exprs) => SList(SSymbol("and") :: exprs.map(rec).toList)
      case Or(exprs) => SList(SSymbol("or") :: exprs.map(rec).toList)
      case Not(expr) => SList(SSymbol("not"), rec(expr))
      case Equals(l,r) => SList(SSymbol("="), rec(l), rec(r))
      case IntLiteral(v) => SInt(v)
      case BooleanLiteral(v) => SSymbol(v.toString) //TODO: maybe need some builtin type here
      case StringLiteral(s) => SString(s)

      case Implies(l,r) => SList(SSymbol("=>"), rec(l), rec(r))
      case Iff(l,r) => SList(SSymbol("="), rec(l), rec(r))

      case Plus(l,r) => SList(SSymbol("+"), rec(l), rec(r))
      case UMinus(expr) => SList(SSymbol("-"), rec(expr))
      case Minus(l,r) => SList(SSymbol("-"), rec(l), rec(r))
      case Times(l,r) => SList(SSymbol("*"), rec(l), rec(r))
      case Division(l,r) => SList(SSymbol("div"), rec(l), rec(r))
      case Modulo(l,r) => SList(SSymbol("mod"), rec(l), rec(r))
      case LessThan(l,r) => SList(SSymbol("<"), rec(l), rec(r))
      case LessEquals(l,r) => SList(SSymbol("<="), rec(l), rec(r))
      case GreaterThan(l,r) => SList(SSymbol(">"), rec(l), rec(r))
      case GreaterEquals(l,r) => SList(SSymbol(">="), rec(l), rec(r))

      case IfExpr(c, t, e) => SList(SSymbol("ite"), rec(c), rec(t), rec(e))

      case FunctionInvocation(fd, args) => SList(id2sym(fd.id) :: args.map(rec).toList)

      //case ArrayFill(length, defaultValue) => SList(
      //  SList(SSymbol("as"), SSymbol("const"), tpe2sort(tree.getType)),
      //  rec(defaultValue)
      //)
      //case ArrayMake(defaultValue) => SList(
      //  SList(SSymbol("as"), SSymbol("const"), tpe2sort(tree.getType)),
      //  rec(defaultValue)
      //)
      //case ArraySelect(array, index) => SList(SSymbol("select"), rec(array), rec(index))
      //case ArrayUpdated(array, index, newValue) => SList(SSymbol("store"), rec(array), rec(index), rec(newValue))

      case CaseClass(ccd, args) if args.isEmpty => id2sym(ccd.id)
      case CaseClass(ccd, args) => SList(id2sym(ccd.id) :: args.map(rec(_)).toList)
      case CaseClassSelector(_, arg, field) => SList(id2sym(field), rec(arg))

      case CaseClassInstanceOf(ccd, arg) => {
        val name = id2sym(ccd.id)
        val testerName = SSymbol("is-" + name.s)
        SList(testerName, rec(arg))
      }
      case o => sys.error("TODO converting to smtlib: " + o)
    }

    val res = rec(tree)
    (res, freeVars)
  }
}
