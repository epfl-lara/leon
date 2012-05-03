package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object ArrayTransformation extends Pass {

  val description = "Add bound checking for array access and remove side effect array update operations"

  def apply(pgm: Program): Program = {

    val allFuns = pgm.definedFunctions
    allFuns.foreach(fd => fd.body.map(body => {
      val newBody = searchAndReplaceDFS{
        case Let(i, v, b) => {println("let i: " + v.getType); v.getType match {
          case ArrayType(_) => {
            println("this is array type")
            Some(LetVar(i, v, b))
          }
          case _ => None
        }}
        case sel@ArraySelect(ar, i) => {
          Some(IfExpr(
            And(GreaterEquals(i, i), LessThan(i, i)),
            sel, 
            Error("Array out of bound access").setType(sel.getType)
          ).setType(sel.getType))
        }
        case ArrayUpdate(ar, i, v) => {
          Some(IfExpr(
            And(GreaterEquals(i, i), LessThan(i, i)),
            Assignment(ar.asInstanceOf[Variable].id, ArrayUpdated(ar, i, v).setType(ar.getType)),
            Error("Array out of bound access").setType(UnitType)
          ).setType(UnitType))
        }
        case _ => None
      }(body)
      fd.body = Some(newBody)
    }))
    pgm
  }

  private def transform(expr: Expr): Expr = expr match {
    case fill@ArrayFill(length, default) => {
      var rLength = transform(length)
      val rDefault = transform(default)
      val rFill = ArrayFill(length, default).setType(fill.getType)
      Tuple(Seq(rFill, length)).setType(TupleType(Seq(fill.getType, Int32Type)))
    }
    case sel@ArraySelect(a, i) => {
      val ar = transform(a)
      val ir = transform(i)
      val length = TupleSelect(ar, 2)
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        ArraySelect(TupleSelect(ar, 1), ir).setType(sel.getType),
        Error("Array out of bound access").setType(sel.getType)
      ).setType(sel.getType)
    }
    case ArrayUpdate(a, i, v) => {
      val ar = transform(a)
      val ir = transform(i)
      val vr = transform(v)
      val length = TupleSelect(ar, 2)
      val  = Tuple
      Some(IfExpr(
        And(GreaterEquals(i, i), LessThan(i, i)),
        Assignment(ar.asInstanceOf[Variable].id, ArrayUpdated(ar, i, v).setType(ar.getType)),
        Error("Array out of bound access").setType(UnitType)
      ).setType(UnitType))
    }

    case Let(i, v, b) => v.getType match {
      case ArrayType(_) => Some(LetVar(i, v, b))
      case _ => None
    }
    case LetVar(id, e, b) =>

    case ite@IfExpr(cond, tExpr, eExpr) => 

    case m @ MatchExpr(scrut, cses) => 
    case LetDef(fd, b) => 

    case n @ NAryOperator(args, recons) => {
    case b @ BinaryOperator(a1, a2, recons) => 
    case u @ UnaryOperator(a, recons) => 

    case (t: Terminal) => 
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)

  }

}
