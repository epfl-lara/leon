package leon
package xlang

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Extractors._
import leon.purescala.PrettyPrinter._

object Trees {

  private def ind(sb: StringBuffer, lvl: Int) : StringBuffer = {
    sb.append("  " * lvl)
    sb
  }

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    //val t = last.getType
    //if(t != Untyped)
     // setType(t)

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val Block(args, rest) = this
      Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
    }

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      sb.append("{\n")
      (exprs :+ last).foreach(e => {
        ind(sb, lvl+1)
        rp(e, sb, lvl+1)
        sb.append("\n")
      })
      ind(sb, lvl)
      sb.append("}\n")
      sb
    }

  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable with PrettyPrintable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }
    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      var nsb: StringBuffer = sb
      nsb.append("(")
      nsb.append(varId.name)
      nsb.append(" = ")
      nsb = rp(expr, nsb, lvl)
      nsb.append(")")
      nsb
    }
  }
  case class While(cond: Expr, body: Expr) extends Expr with FixedType with ScalacPositional with BinaryExtractable with PrettyPrintable {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((cond, body, (t1, t2) => While(t1, t2).setInvariant(this.invariant).setPosInfo(this)))
    }

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      invariant match {
        case Some(inv) => {
          sb.append("\n")
          ind(sb, lvl)
          sb.append("@invariant: ")
          rp(inv, sb, lvl)
          sb.append("\n")
          ind(sb, lvl)
        }
        case None =>
      }
      sb.append("while(")
      rp(cond, sb, lvl)
      sb.append(")\n")
      ind(sb, lvl+1)
      rp(body, sb, lvl+1)
      sb.append("\n")
    }

  }

  case class Epsilon(pred: Expr) extends Expr with ScalacPositional with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr).setType(this.getType).setPosInfo(this)))
    }

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      var nsb = sb
      nsb.append("epsilon(x" + this.posIntInfo._1 + "_" + this.posIntInfo._2 + ". ")
      nsb = rp(pred, nsb, lvl)
      nsb.append(")")
      nsb
    }

  }
  case class EpsilonVariable(pos: (Int, Int)) extends Expr with Terminal with PrettyPrintable {
    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      val (row, col) = pos
      sb.append("x" + row + "_" + col)
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

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      val LetVar(b,d,e) = this
      sb.append("(letvar (" + b + " := ");
      rp(d, sb, lvl)
      sb.append(") in\n")
      ind(sb, lvl+1)
      rp(e, sb, lvl+1)
      sb.append(")")
      sb
    }
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e)))
    }

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      sb.append("waypoint_" + i + "(")
      rp(expr, sb, lvl)
      sb.append(")")
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

    def pp(sb: StringBuffer, lvl: Int, rp: (Expr, StringBuffer, Int) => StringBuffer): StringBuffer = {
      rp(array, sb, lvl)
      sb.append("(")
      rp(index, sb, lvl)
      sb.append(") = ")
      rp(newValue, sb, lvl)
    }
  }
}
