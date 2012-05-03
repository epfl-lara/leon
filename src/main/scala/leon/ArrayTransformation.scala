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
      val newBody = transform(body)
      fd.body = Some(newBody)
    }))
    pgm
  }

  private var id2id: Map[Identifier, Identifier] = Map()

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
      val length = TupleSelect(ar, 2).setType(Int32Type)
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
      val Variable(id) = ar
      val length = TupleSelect(ar, 2).setType(Int32Type)
      val array = TupleSelect(ar, 1).setType(ArrayType(v.getType))
      //val Tuple(Seq(Variable(id), length)) = ar
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        Block(Seq(Assignment(id, Tuple(Seq(ArrayUpdated(array, i, v).setType(array.getType), length)).setType(TupleType(Seq(array.getType, Int32Type))))), IntLiteral(0)),
        Error("Array out of bound access").setType(Int32Type)
      ).setType(Int32Type)
    }

    case Let(i, v, b) => {
      val vr = transform(v)
      v.getType match {
        case ArrayType(_) => {
          val freshIdentifier = FreshIdentifier("t").setType(vr.getType)
          id2id += (i -> freshIdentifier)
          val br = transform(b)
          LetVar(freshIdentifier, vr, br)
        }
        case _ => {
          val br = transform(b)
          Let(i, vr, br)
        }
      }
    }
    //case LetVar(id, e, b) =>

    //case ite@IfExpr(cond, tExpr, eExpr) => 

    //case m @ MatchExpr(scrut, cses) => 
    //case LetDef(fd, b) => 

    case n @ NAryOperator(args, recons) => recons(args.map(transform)).setType(n.getType)
    case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2)).setType(b.getType)
    case u @ UnaryOperator(a, recons) => recons(transform(a)).setType(u.getType)

    case v @ Variable(id) => if(id2id.isDefinedAt(id)) Variable(id2id(id)) else v
    case (t: Terminal) => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)

  }

}
