package leon
package xlang

import leon.purescala.Common._
import leon.purescala.TypeTrees._
import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.Extractors._

object Trees {

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr {
    //val t = last.getType
    //if(t != Untyped)
     // setType(t)
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType {
    val fixedType = UnitType
  }
  case class While(cond: Expr, body: Expr) extends Expr with FixedType with ScalacPositional {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }
  }

  case class Epsilon(pred: Expr) extends Expr with ScalacPositional
  case class EpsilonVariable(pos: (Int, Int)) extends Expr with Terminal

  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr

  //the difference between ArrayUpdate and ArrayUpdated is that the former has a side effect while the latter is the functional version
  //ArrayUpdate should be eliminated soon in the analysis while ArrayUpdated is kept all the way to the backend
  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with ScalacPositional with FixedType {
    val fixedType = UnitType
  }
}
