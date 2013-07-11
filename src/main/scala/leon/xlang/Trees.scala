/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package xlang

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Extractors._
import leon.purescala.{PrettyPrinter, PrettyPrintable}
import leon.purescala.ScalaPrinter._

object Trees {

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
    sb.append("  " * lvl)
    sb
  }

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable with PrettyPrintable with ScalaPrintable with FixedType {
    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val Block(args, rest) = this
      Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("{\n")
      (exprs :+ last).foreach(e => {
        printer.ind(lvl+1)
        printer.pp(e, lvl+1)
        printer.append("\n")
      })
      printer.ind(lvl)
      printer.append("}\n")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      sb.append("{\n")
      (exprs :+ last).foreach(e => {
        ind(sb, lvl+1)
        ep(e, sb, lvl+1)
        sb.append("\n")
      })
      ind(sb, lvl)
      sb.append("}\n")
      sb
    }

    val fixedType = last.getType
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable with ScalaPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("(")
      printer.append(varId.name)
      printer.append(" = ")
      printer.pp(expr,lvl)
      printer.append(")")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      var nsb: StringBuffer = sb
      nsb.append("(")
      nsb.append(varId.name)
      nsb.append(" = ")
      ep(expr, nsb, lvl)
      nsb.append(")")
      nsb
    }
  }
  case class While(cond: Expr, body: Expr) extends Expr with FixedType with ScalacPositional with BinaryExtractable with PrettyPrintable with ScalaPrintable {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((cond, body, (t1, t2) => While(t1, t2).setInvariant(this.invariant).setPosInfo(this)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      invariant match {
        case Some(inv) => {
          printer.append("\n")
          printer.ind(lvl)
          printer.append("@invariant: ")
          printer.pp(inv, lvl)
          printer.append("\n")
          printer.ind(lvl)
        }
        case None =>
      }
      printer.append("while(")
      printer.pp(cond, lvl)
      printer.append(")\n")
      printer.ind(lvl+1)
      printer.pp(body, lvl+1)
      printer.append("\n")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      invariant match {
        case Some(inv) => {
          sb.append("\n")
          ind(sb, lvl)
          sb.append("@invariant: ")
          ep(inv, sb, lvl)
          sb.append("\n")
          ind(sb, lvl)
        }
        case None =>
      }
      sb.append("while(")
      ep(cond, sb, lvl)
      sb.append(")\n")
      ind(sb, lvl+1)
      ep(body, sb, lvl+1)
      sb.append("\n")
    }

  }

  case class Epsilon(pred: Expr) extends Expr with ScalacPositional with UnaryExtractable with PrettyPrintable with ScalaPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr).setType(this.getType).setPosInfo(this)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("epsilon(x" + this.posIntInfo._1 + "_" + this.posIntInfo._2 + ". ")
      printer.pp(pred, lvl)
      printer.append(")")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      sys.error("Not Scala Code")
    }

  }
  case class EpsilonVariable(pos: (Int, Int)) extends Expr with Terminal with PrettyPrintable with ScalaPrintable {

    def printWith(lvl: Int, printer: PrettyPrinter) {
      val (row, col) = pos
      printer.append("x" + row + "_" + col)
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      val (row, col) = pos
      sb.append("x" + row + "_" + col)
    }
  }

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr with BinaryExtractable with PrettyPrintable with ScalaPrintable {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      val LetVar(binders, expr, body) = this
      Some((expr, body, (e: Expr, b: Expr) => LetVar(binders, e, b)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      val LetVar(b,d,e) = this
      printer.append("(letvar (" + b + " := ");
      printer.pp(d, lvl)
      printer.append(") in\n")
      printer.ind(lvl+1)
      printer.pp(e, lvl+1)
      printer.append(")")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      val LetVar(b,d,e) = this
      sb.append("locally {\n")
      ind(sb, lvl+1)
      sb.append("var " + b + " = ")
      ep(d, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl+1)
      ep(e, sb, lvl+1)
      sb.append("\n")
      ind(sb, lvl)
      sb.append("}\n")
      ind(sb, lvl)
    }
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr with NAryExtractable with PrettyPrintable with ScalaPrintable {
    val et = body.getType
    if(et != Untyped)
      setType(et)

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      fd.body match {
        case Some(b) =>
          (fd.precondition, fd.postcondition) match {
            case (None, None) =>
                Some((Seq(b, body), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.body = Some(as(0))
                  //LetDef(nfd, as(1))
                  fd.body = Some(as(0))
                  LetDef(fd, as(1))
                }))
            case (Some(pre), None) =>
                Some((Seq(b, body, pre), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.body = Some(as(0))
                  //nfd.precondition = Some(as(2))
                  //LetDef(nfd, as(1))
                  fd.body = Some(as(0))
                  fd.precondition = Some(as(2))
                  LetDef(fd, as(1))
                }))
            case (None, Some(post)) =>
                Some((Seq(b, body, post), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.body = Some(as(0))
                  //nfd.postcondition = Some(as(2))
                  //LetDef(nfd, as(1))
                  fd.body = Some(as(0))
                  fd.postcondition = Some(as(2))
                  LetDef(fd, as(1))
                }))
            case (Some(pre), Some(post)) =>
                Some((Seq(b, body, pre, post), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.body = Some(as(0))
                  //nfd.precondition = Some(as(2))
                  //nfd.postcondition = Some(as(3))
                  //LetDef(nfd, as(1))
                  fd.body = Some(as(0))
                  fd.precondition = Some(as(2))
                  fd.postcondition = Some(as(3))
                  LetDef(fd, as(1))
                }))
          }
            
        case None => //case no body, we still need to handle remaining cases
          (fd.precondition, fd.postcondition) match {
            case (None, None) =>
                Some((Seq(body), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //LetDef(nfd, as(0))
                  LetDef(fd, as(0))
                }))
            case (Some(pre), None) =>
                Some((Seq(body, pre), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.precondition = Some(as(1))
                  //LetDef(nfd, as(0))
                  fd.precondition = Some(as(1))
                  LetDef(fd, as(0))
                }))
            case (None, Some(post)) =>
                Some((Seq(body, post), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.postcondition = Some(as(1))
                  //LetDef(nfd, as(0))
                  fd.postcondition = Some(as(1))
                  LetDef(fd, as(0))
                }))
            case (Some(pre), Some(post)) =>
                Some((Seq(body, pre, post), (as: Seq[Expr]) => {
                  //val nfd = new FunDef(fd.id, fd.returnType, fd.args)
                  //nfd.precondition = Some(as(1))
                  //nfd.postcondition = Some(as(2))
                  //LetDef(nfd, as(0))
                  fd.precondition = Some(as(1))
                  fd.postcondition = Some(as(2))
                  LetDef(fd, as(0))
                }))
          }
      }
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("\n")
      printer.pp(fd, lvl+1)
      printer.append("\n")
      printer.append("\n")
      printer.ind(lvl)
      printer.pp(body, lvl)
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      sb.append("{\n")
      dp(fd, sb, lvl+1)
      sb.append("\n")
      sb.append("\n")
      ind(sb, lvl)
      ep(body, sb, lvl)
      sb.append("}\n")
      sb
    }

  }

  case class Waypoint(i: Int, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable with ScalaPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e)))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.append("waypoint_" + i + "(")
      printer.pp(expr, lvl)
      printer.append(")")
    }

    def ppScala(sb: StringBuffer, lvl: Int, 
      ep: (Expr, StringBuffer, Int) => Unit, 
      tp: (TypeTree, StringBuffer, Int) => Unit,
      dp: (Definition, StringBuffer, Int) => Unit
    ): StringBuffer = {
      sys.error("Not Scala Code")
    }
  }

  //the difference between ArrayUpdate and ArrayUpdated is that the former has a side effect while the latter is the functional version
  //ArrayUpdate should be eliminated soon in the analysis while ArrayUpdated is kept all the way to the backend
  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with ScalacPositional with FixedType with NAryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val ArrayUpdate(t1, t2, t3) = this
      Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
    }

    def printWith(lvl: Int, printer: PrettyPrinter) {
      printer.pp(array, lvl)
      printer.append("(")
      printer.pp(index, lvl)
      printer.append(") = ")
      printer.pp(newValue, lvl)
    }
  }

}
