/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Types._

class BagEncoder(ctx: LeonContext, p: Program) extends TheoryEncoder {
  val Bag = p.library.lookupUnique[CaseClassDef]("leon.theories.Bag")

  val Get        = p.library.lookupUnique[FunDef]("leon.theories.Bag.get")
  val Add        = p.library.lookupUnique[FunDef]("leon.theories.Bag.add")
  val Union      = p.library.lookupUnique[FunDef]("leon.theories.Bag.union")
  val Difference = p.library.lookupUnique[FunDef]("leon.theories.Bag.difference")
  val Intersect  = p.library.lookupUnique[FunDef]("leon.theories.Bag.intersect")
  val BagEquals  = p.library.lookupUnique[FunDef]("leon.theories.Bag.equals")

  val encoder = new Encoder {
    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case FiniteBag(elems, tpe) =>
        val newTpe = transform(tpe)
        val id = FreshIdentifier("x", newTpe, true)
        Some(CaseClass(Bag.typed(Seq(newTpe)), Seq(Lambda(Seq(ValDef(id)),
          elems.foldRight[Expr](InfiniteIntegerLiteral(0).copiedFrom(e)) { case ((k, v), ite) =>
            IfExpr(Equals(Variable(id), transform(k)), transform(v), ite).copiedFrom(e)
          }))).copiedFrom(e))

      case BagAdd(bag, elem) =>
        val BagType(base) = bag.getType
        Some(FunctionInvocation(Add.typed(Seq(transform(base))), Seq(transform(bag), transform(elem))).copiedFrom(e))

      case MultiplicityInBag(elem, bag) =>
        val BagType(base) = bag.getType
        Some(FunctionInvocation(Get.typed(Seq(transform(base))), Seq(transform(bag), transform(elem))).copiedFrom(e))

      case BagIntersection(b1, b2) =>
        val BagType(base) = b1.getType
        Some(FunctionInvocation(Intersect.typed(Seq(transform(base))), Seq(transform(b1), transform(b2))).copiedFrom(e))

      case BagUnion(b1, b2) =>
        val BagType(base) = b1.getType
        Some(FunctionInvocation(Union.typed(Seq(transform(base))), Seq(transform(b1), transform(b2))).copiedFrom(e))

      case BagDifference(b1, b2) =>
        val BagType(base) = b1.getType
        Some(FunctionInvocation(Difference.typed(Seq(transform(base))), Seq(transform(b1), transform(b2))).copiedFrom(e))

      case Equals(b1, b2) if b1.getType.isInstanceOf[BagType] =>
        val BagType(base) = b1.getType
        Some(FunctionInvocation(BagEquals.typed(Seq(transform(base))), Seq(transform(b1), transform(b2))).copiedFrom(e))

      case _ => None
    }

    override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
      case BagType(base) => Some(Bag.typed(Seq(transform(base))).copiedFrom(tpe))
      case _ => None
    }
  }

  val decoder = new Decoder {
    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case cc @ CaseClass(CaseClassType(Bag, Seq(tpe)), args) =>
        Some(FiniteBag(args(0) match {
          case FiniteLambda(mapping, dflt, tpe) =>
            if (dflt != InfiniteIntegerLiteral(0))
              throw new Unsupported(cc, "Bags can't have default value " + dflt.asString(ctx))(ctx)
            mapping.map { case (ks, v) => transform(ks.head) -> transform(v) }.toMap

          case Lambda(Seq(ValDef(id)), body) =>
            def rec(expr: Expr): Map[Expr, Expr] = expr match {
              case IfExpr(Equals(`id`, k), v, elze) => rec(elze) + (transform(k) -> transform(v))
              case InfiniteIntegerLiteral(v) if v == 0 => Map.empty
              case _ => throw new Unsupported(expr, "Bags can't have default value " + expr.asString(ctx))(ctx)
            }

            rec(body)

          case f => scala.sys.error("Unexpected function " + f.asString(ctx))
        }, transform(tpe)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(Add, Seq(_)), Seq(bag, elem)) =>
        Some(BagAdd(transform(bag), transform(elem)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(Get, Seq(_)), Seq(bag, elem)) =>
        Some(MultiplicityInBag(transform(elem), transform(bag)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(Intersect, Seq(_)), Seq(b1, b2)) =>
        Some(BagIntersection(transform(b1), transform(b2)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(Union, Seq(_)), Seq(b1, b2)) =>
        Some(BagUnion(transform(b1), transform(b2)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(Difference, Seq(_)), Seq(b1, b2)) =>
        Some(BagDifference(transform(b1), transform(b2)).copiedFrom(e))

      case FunctionInvocation(TypedFunDef(BagEquals, Seq(_)), Seq(b1, b2)) =>
        Some(Equals(transform(b1), transform(b2)).copiedFrom(e))

      case _ => None
    }

    override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
      case CaseClassType(Bag, Seq(base)) => Some(BagType(transform(base)).copiedFrom(tpe))
      case _ => None
    }

    override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
      case CaseClassPattern(b, CaseClassType(Bag, Seq(tpe)), Seq(sub)) =>
        throw new Unsupported(pat, "Can't translate Bag case class pattern")(ctx)
      case _ => super.transform(pat)
    }
  }
}
