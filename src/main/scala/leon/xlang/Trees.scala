package leon
package xlang

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Extractors._

object Trees {

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with NAryExtractable {
    //val t = last.getType
    //if(t != Untyped)
     // setType(t)

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val Block(args, rest) = this
      Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
    }
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType with UnaryExtractable {
    val fixedType = UnitType

    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, Assignment(varId, _)))
    }
  }
  case class While(cond: Expr, body: Expr) extends Expr with FixedType with ScalacPositional with BinaryExtractable {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      Some((cond, body, (t1, t2) => While(t1, t2).setInvariant(this.invariant).setPosInfo(this)))
    }
  }

  case class Epsilon(pred: Expr) extends Expr with ScalacPositional with UnaryExtractable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((pred, (expr: Expr) => Epsilon(expr).setType(this.getType).setPosInfo(this)))
    }
  }
  case class EpsilonVariable(pos: (Int, Int)) extends Expr with Terminal

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr with BinaryExtractable {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)

    def extract: Option[(Expr, Expr, (Expr, Expr)=>Expr)] = {
      val LetVar(binders, expr, body) = this
      Some((expr, body, (e: Expr, b: Expr) => LetVar(binders, e, b)))
    }
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr with UnaryExtractable {
    def extract: Option[(Expr, (Expr)=>Expr)] = {
      Some((expr, (e: Expr) => Waypoint(i, e)))
    }
  }

  //the difference between ArrayUpdate and ArrayUpdated is that the former has a side effect while the latter is the functional version
  //ArrayUpdate should be eliminated soon in the analysis while ArrayUpdated is kept all the way to the backend
  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with ScalacPositional with FixedType with NAryExtractable {
    val fixedType = UnitType

    def extract: Option[(Seq[Expr], (Seq[Expr])=>Expr)] = {
      val ArrayUpdate(t1, t2, t3) = this
      Some((Seq(t1,t2,t3), (as: Seq[Expr]) => ArrayUpdate(as(0), as(1), as(2))))
    }
  }
}
