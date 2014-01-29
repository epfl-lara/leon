package leon

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

package object smtlib {

  private[smtlib] def id2sym(id: Identifier): SSymbol = SSymbol(id.uniqueName)
  //return a series of declarations, an expression that defines the function, 
  //and the seq of asserts for pre/post-conditions


  def tpe2sort[smtlib](tpe: TypeTree): SExpr = tpe match {
    case Int32Type => SSymbol("Int")
    case BooleanType => SSymbol("Bool")
    case ArrayType(baseTpe) => SList(SSymbol("Array"), SSymbol("Int"), tpe2sort(baseTpe))
    case AbstractClassType(abs) => id2sym(abs.id)
    case _ => sys.error("TODO tpe2sort: " + tpe)
  }

}
