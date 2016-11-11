/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._
import purescala.Types._
import purescala.Definitions._
import leon.utils.Bijection
import leon.purescala.TypeOps

object ArrayEncoder {
  private val arrayTypeParam = TypeParameter.fresh("A")
  val ArrayCaseClass = new CaseClassDef(FreshIdentifier("InternalArray"), Seq(TypeParameterDef(arrayTypeParam)), None, false)
  val rawArrayField = FreshIdentifier("raw", RawArrayType(Int32Type, arrayTypeParam))
  val lengthField = FreshIdentifier("length", Int32Type)
  ArrayCaseClass.setFields(Seq(ValDef(rawArrayField), ValDef(lengthField)))

  val thisPointer = FreshIdentifier("thisArray", ArrayCaseClass.typed)
  val invariant = new FunDef(
    FreshIdentifier("invariantInternalArray"),
    Seq(TypeParameterDef(arrayTypeParam)),
    Seq(ValDef(thisPointer)),
    BooleanType)
  invariant.body = 
    Some(GreaterEquals(
      CaseClassSelector(ArrayCaseClass.typed, thisPointer.toVariable, lengthField),
      IntLiteral(0)))

  ArrayCaseClass.setInvariant(invariant)


  def getLength(e: Expr): Expr = {
    CaseClassSelector(e.getType.asInstanceOf[CaseClassType], e, lengthField)
  }
  def select(e: Expr, i: Expr): Expr = {
    RawArraySelect(
      CaseClassSelector(e.getType.asInstanceOf[CaseClassType], e, rawArrayField),
      i)
  }

}

class ArrayEncoder(ctx: LeonContext, p: Program) extends TheoryEncoder {
  import ArrayEncoder._

  val encoder = new Encoder {
    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case al @ ArrayLength(a) =>
        val ArrayType(base) = a.getType
        val ra = transform(a)
        Some(CaseClassSelector(ArrayCaseClass.typed(Seq(base)), ra, lengthField))

      case al @ ArraySelect(a, i) =>
        val ArrayType(base) = a.getType
        val ra = transform(a)
        val ri = transform(i)
        val raw = CaseClassSelector(transform(a.getType).asInstanceOf[CaseClassType], ra, rawArrayField)
        Some(RawArraySelect(raw, ri))

      case al @ ArrayUpdated(a, i, e) =>
        val ra = transform(a)
        val ri = transform(i)
        val re = transform(e)

        val length = CaseClassSelector(transform(a.getType).asInstanceOf[CaseClassType], ra, lengthField)
        val raw = CaseClassSelector(transform(a.getType).asInstanceOf[CaseClassType], ra, rawArrayField)

        Some(CaseClass(transform(a.getType).asInstanceOf[CaseClassType], Seq(RawArrayUpdated(raw, ri, re), length)))

      case a @ FiniteArray(elems, oDef, size) =>

        val tpe @ ArrayType(to) = a.getType
        val default: Expr = transform(oDef.getOrElse(simplestValue(to)))

        val raw = RawArrayValue(Int32Type, elems.map {
          case (k, v) => IntLiteral(k) -> transform(v)
        }, default)
        Some(CaseClass(ArrayCaseClass.typed(Seq(to)), Seq(raw, transform(size))))

      case _ => None
    }

    override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
      case ArrayType(base) => Some(ArrayCaseClass.typed(Seq(base)))
      case _ => None
    }

  }


  val decoder = new Decoder {

    private def fromRaw(raw: Expr, length: Expr): Expr = {
      val RawArrayValue(baseType, elems, default) = raw
      val IntLiteral(size) = length
      if (size < 0) {
        //TODO: maybe we should return a negative length array, and handle it in evaluator.
        //      but as such, it should be safe as negative array should never be returned
        //      by the solver, except on lucky tests, but then any model is safe as it is
        //      evaluated to check its validity
        EmptyArray(baseType)
        //throw new Exception("Cannot build an array of negative length: " + size)
      } else if (size > 10) {
        val definedElements = elems.collect {
          case (IntLiteral(i), value) => (i, value)
        }
        finiteArray(definedElements, Some(default, IntLiteral(size)), baseType)

      } else {
        val entries = for (i <- 0 to size - 1) yield elems.getOrElse(IntLiteral(i), default)

        finiteArray(entries.toList, None, baseType)
      }
    }

    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case cc @ CaseClass(cct, args) if cct.classDef == ArrayCaseClass =>
        val Seq(rawArray, length) = args
        val leonArray = fromRaw(rawArray, length)
        Some(leonArray)

      //  Some(StringLiteral(convertToString(cc)).copiedFrom(cc))
      //case FunctionInvocation(SizeI, Seq(a)) =>
      //  Some(StringLength(transform(a)).copiedFrom(e))
      //case FunctionInvocation(Size, Seq(a)) =>
      //  Some(StringBigLength(transform(a)).copiedFrom(e))
      //case FunctionInvocation(Concat, Seq(a, b)) =>
      //  Some(StringConcat(transform(a), transform(b)).copiedFrom(e))
      //case FunctionInvocation(SliceI, Seq(a, from, to)) =>
      //  Some(SubString(transform(a), transform(from), transform(to)).copiedFrom(e))
      //case FunctionInvocation(Slice, Seq(a, from, to)) =>
      //  Some(BigSubString(transform(a), transform(from), transform(to)).copiedFrom(e))
      //case FunctionInvocation(TakeI, Seq(FunctionInvocation(DropI, Seq(a, start)), length)) =>
      //  val rstart = transform(start)
      //  Some(SubString(transform(a), rstart, plus(rstart, transform(length))).copiedFrom(e))
      //case FunctionInvocation(Take, Seq(FunctionInvocation(Drop, Seq(a, start)), length)) =>
      //  val rstart = transform(start)
      //  Some(BigSubString(transform(a), rstart, plus(rstart, transform(length))).copiedFrom(e))
      //case FunctionInvocation(TakeI, Seq(a, length)) =>
      //  Some(SubString(transform(a), IntLiteral(0), transform(length)).copiedFrom(e))
      //case FunctionInvocation(Take, Seq(a, length)) =>
      //  Some(BigSubString(transform(a), InfiniteIntegerLiteral(0), transform(length)).copiedFrom(e))
      //case FunctionInvocation(DropI, Seq(a, count)) =>
      //  val ra = transform(a)
      //  Some(SubString(ra, transform(count), StringLength(ra)).copiedFrom(e))
      //case FunctionInvocation(Drop, Seq(a, count)) =>
      //  val ra = transform(a)
      //  Some(BigSubString(ra, transform(count), StringBigLength(ra)).copiedFrom(e))
      //case FunctionInvocation(FromInt, Seq(a)) =>
      //  Some(Int32ToString(transform(a)).copiedFrom(e))
      //case FunctionInvocation(FromBigInt, Seq(a)) =>
      //  Some(IntegerToString(transform(a)).copiedFrom(e))
      //case FunctionInvocation(FromChar, Seq(a)) =>
      //  Some(CharToString(transform(a)).copiedFrom(e))
      //case FunctionInvocation(FromBoolean, Seq(a)) =>
      //  Some(BooleanToString(transform(a)).copiedFrom(e))
      case _ => None
    }


    override def transformType(tpe: TypeTree): Option[TypeTree] = tpe match {
      //case String | StringCons | StringNil => Some(StringType)
      case _ => None
    }

    //override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
    //  case CaseClassPattern(b, StringNil, Seq()) =>
    //    val newBinder = b map transform
    //    (LiteralPattern(newBinder , StringLiteral("")), (b zip newBinder).filter(p => p._1 != p._2).toMap)

    //  case CaseClassPattern(b, StringCons, Seq(LiteralPattern(_, CharLiteral(elem)), sub)) => transform(sub) match {
    //    case (LiteralPattern(_, StringLiteral(s)), binders) =>
    //      val newBinder = b map transform
    //      (LiteralPattern(newBinder, StringLiteral(elem + s)), (b zip newBinder).filter(p => p._1 != p._2).toMap ++ binders)
    //    case (e, binders) =>
    //      throw new Unsupported(pat, "Failed to parse pattern back as string: " + e)(ctx)
    //  }

    //  case _ => super.transform(pat)
    //}
  }
}

