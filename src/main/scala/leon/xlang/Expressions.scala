/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import purescala.Common._
import purescala.Types._
import purescala.Expressions._
import purescala.Extractors._
import purescala.{PrettyPrintable, PrinterContext}
import utils._

object Expressions {
  import purescala.PrinterHelpers._

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      Some((exprs :+ last, exprs => Block(exprs.init, exprs.last)))
    }

    override def getPos = {
      Position.between(exprs.head.getPos, last.getPos)
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""|{
          |  ${nary(exprs :+ last, "\n")}
          |}"""
    }

    val getType = last.getType
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with UnaryExtractable with PrettyPrintable {
    val getType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"$varId = $expr;"
    }
  }

  case class While(cond: Expr, body: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    val getType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Seq[Expr], Seq[Expr]=>Expr)] = {
      Some((Seq(cond, body) ++ invariant, {
        case Seq(e1, e2) => While(e1, e2).setPos(this)
        case Seq(e1, e2, e3) => While(e1, e2).setInvariant(e3).setPos(this)
      }))
    }

    def printWith(implicit pctx: PrinterContext) {
      invariant match {
        case Some(inv) =>
          p"""|@invariant($inv)
              |"""
        case None =>
      }

      p"""|while($cond) {
          |  $body
          |}"""
    }
  }

  case class Epsilon(pred: Expr, tpe: TypeTree) extends Expr with UnaryExtractable with PrettyPrintable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr, this.getType).setPos(this)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"epsilon(x${getPos.line}_${getPos.col}. $pred)"
    }

    val getType = tpe
  }

  case class EpsilonVariable(pos: Position, tpe: TypeTree) extends Expr with Terminal with PrettyPrintable {

    def printWith(implicit pctx: PrinterContext) {
      p"x${pos.line}_${pos.col}"
    }

    val getType = tpe
  }

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr with BinaryExtractable with PrettyPrintable {
    val getType = body.getType

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((value, body, (e: Expr, b: Expr) => LetVar(binder, e, b)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"""|locally {
          |  var $binder = $value
          |  $body
          |}"""
    }
  }

  case class Waypoint(i: Int, expr: Expr, tpe: TypeTree) extends Expr with UnaryExtractable with PrettyPrintable{
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e, tpe)))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"waypoint_$i($expr)"
    }

    val getType = tpe
  }

  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with NAryExtractable with PrettyPrintable {
    val getType = UnitType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val ArrayUpdate(t1, t2, t3) = this
      Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
    }

    def printWith(implicit pctx: PrinterContext) {
      p"$array($index) = $newValue"
    }
  }

}
