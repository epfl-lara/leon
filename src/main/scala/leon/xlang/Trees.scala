/* Copyright 2009-2013 EPFL, Lausanne */
package leon
package xlang

import purescala.Common._
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._
import purescala.Extractors._
import purescala.{PrettyPrinter, PrettyPrintable, ScalaPrinter}
import utils._

object Trees {

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
    sb.append("  " * lvl)
    sb
  }

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable with PrettyPrintable with FixedType {
    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val Block(args, rest) = this
      Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("{\n")
      (exprs :+ last).foreach(e => {
        printer.ind(lvl+1)
        printer.pp(e, Some(this))(lvl+1)
        printer.append("\n")
      })
      printer.ind(lvl)
      printer.append("}\n")
    }

    val fixedType = last.getType
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("(")
      printer.append(varId.name)
      printer.append(" = ")
      printer.pp(expr, Some(this))
      printer.append(")")
    }
  }

  case class While(cond: Expr, body: Expr) extends Expr with FixedType with BinaryExtractable with PrettyPrintable {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((cond, body, (t1, t2) => While(t1, t2).setInvariant(this.invariant).setPos(this)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      invariant match {
        case Some(inv) => {
          printer.append("\n")
          printer.ind
          printer.append("@invariant: ")
          printer.pp(inv, Some(this))
          printer.append("\n")
          printer.ind
        }
        case None =>
      }
      printer.append("while(")
      printer.pp(cond, Some(this))
      printer.append(")\n")
      printer.ind(lvl+1)
      printer.pp(body, Some(this))(lvl+1)
      printer.append("\n")
    }
  }

  case class Epsilon(pred: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr).setType(this.getType).setPos(this)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer match {
        case _: ScalaPrinter =>
          sys.error("Not Scala Code")

        case _ =>
          printer.append("epsilon(x" + this.getPos.line + "_" + this.getPos.col + ". ")
          printer.pp(pred, Some(this))
          printer.append(")")
      }
    }
  }

  case class EpsilonVariable(pos: Position) extends Expr with Terminal with PrettyPrintable{

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.append("x" + pos.line + "_" + pos.col)
    }
  }

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr with BinaryExtractable with PrettyPrintable {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      val LetVar(binders, expr, body) = this
      Some((expr, body, (e: Expr, b: Expr) => LetVar(binders, e, b)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer match {
        case _: ScalaPrinter =>
          val LetVar(b,d,e) = this
          printer.append("locally {\n")
          printer.ind(lvl+1)
          printer.append("var " + b + " = ")
          printer.pp(d, Some(this))(lvl+1)
          printer.append("\n")
          printer.ind(lvl+1)
          printer.pp(e, Some(this))(lvl+1)
          printer.nl
          printer.append("}")
          printer.nl

        case _ =>
          val LetVar(b,d,e) = this
          printer.append("(letvar (" + b + " := ");
          printer.pp(d, Some(this))
          printer.append(") in\n")
          printer.ind(lvl+1)
          printer.pp(e, Some(this))(lvl+1)
          printer.append(")")
      }
    }
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e)))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer match {
        case _: ScalaPrinter =>
          sys.error("Not Scala Code")

        case _ =>
          printer.append("waypoint_" + i + "(")
          printer.pp(expr, Some(this))
          printer.append(")")
      }
    }
  }

  //the difference between ArrayUpdate and ArrayUpdated is that the former has a side effect while the latter is the functional version
  //ArrayUpdate should be eliminated soon in the analysis while ArrayUpdated is kept all the way to the backend
  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val ArrayUpdate(t1, t2, t3) = this
      Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
    }

    def printWith(printer: PrettyPrinter)(implicit lvl: Int) {
      printer.pp(array, Some(this))
      printer.append("(")
      printer.pp(index, Some(this))
      printer.append(") = ")
      printer.pp(newValue, Some(this))
    }
  }

}
