/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Types._
import purescala.Definitions._
import leon.utils.Bijection
import leon.purescala.TypeOps

class ArrayEncoder(ctx: LeonContext, p: Program) extends TheoryEncoder {

  private val arrayTypeParam = TypeParameter.fresh("A")
  val ArrayCaseClass = new CaseClassDef(FreshIdentifier("Array"), Seq(TypeParameterDef(arrayTypeParam)), None, false)
  val rawArrayField = FreshIdentifier("raw", RawArrayType(Int32Type, arrayTypeParam))
  val lengthField = FreshIdentifier("length", Int32Type)
  ArrayCaseClass.setFields(Seq(ValDef(rawArrayField), ValDef(lengthField)))

  
  //val String     = p.library.lookupUnique[ClassDef]("leon.theories.String").typed
  //val StringCons = p.library.lookupUnique[CaseClassDef]("leon.theories.StringCons").typed
  //val StringNil  = p.library.lookupUnique[CaseClassDef]("leon.theories.StringNil").typed

  //val Size   = p.library.lookupUnique[FunDef]("leon.theories.String.size").typed
  //val Take   = p.library.lookupUnique[FunDef]("leon.theories.String.take").typed
  //val Drop   = p.library.lookupUnique[FunDef]("leon.theories.String.drop").typed
  //val Slice  = p.library.lookupUnique[FunDef]("leon.theories.String.slice").typed
  //val Concat = p.library.lookupUnique[FunDef]("leon.theories.String.concat").typed

  //val SizeI   = p.library.lookupUnique[FunDef]("leon.theories.String.sizeI").typed
  //val TakeI   = p.library.lookupUnique[FunDef]("leon.theories.String.takeI").typed
  //val DropI   = p.library.lookupUnique[FunDef]("leon.theories.String.dropI").typed
  //val SliceI  = p.library.lookupUnique[FunDef]("leon.theories.String.sliceI").typed
  //
  //val FromInt      = p.library.lookupUnique[FunDef]("leon.theories.String.fromInt").typed
  //val FromChar     = p.library.lookupUnique[FunDef]("leon.theories.String.fromChar").typed
  //val FromBoolean  = p.library.lookupUnique[FunDef]("leon.theories.String.fromBoolean").typed
  //val FromBigInt   = p.library.lookupUnique[FunDef]("leon.theories.String.fromBigInt").typed
  
  //private val stringBijection = new Bijection[String, Expr]()
  
  //private def convertToString(e: Expr): String  = stringBijection.cachedA(e)(e match {
  //  case CaseClass(_, Seq(CharLiteral(c), l)) => c + convertToString(l)
  //  case CaseClass(_, Seq()) => ""
  //})

  //private def convertFromString(v: String): Expr = stringBijection.cachedB(v) {
  //  v.toList.foldRight(CaseClass(StringNil, Seq())){
  //    case (char, l) => CaseClass(StringCons, Seq(CharLiteral(char), l))
  //  }
  //}

  val encoder = new Encoder {
    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case al @ ArrayLength(a) =>
        val ra = transform(a)
        Some(CaseClassSelector(ra.getType.asInstanceOf[CaseClassType], ra, lengthField))

      //case al @ ArraySelect(a, i) =>
      //  val tpe = normalizeType(a.getType)

      //  val scontent = FunctionApplication(selectors.toB((tpe, 1)), Seq(toSMT(a)))

      //  ArraysEx.Select(scontent, toSMT(i))

      //case al @ ArrayUpdated(a, i, e) =>
      //  val tpe = normalizeType(a.getType)

      //  val sa = toSMT(a)
      //  val ssize = FunctionApplication(selectors.toB((tpe, 0)), Seq(sa))
      //  val scontent = FunctionApplication(selectors.toB((tpe, 1)), Seq(sa))

      //  val newcontent = ArraysEx.Store(scontent, toSMT(i), toSMT(e))

      //  val constructor = constructors.toB(tpe)
      //  FunctionApplication(constructor, Seq(ssize, newcontent))

      //case a @ FiniteArray(elems, oDef, size) =>
      //  val tpe @ ArrayType(to) = normalizeType(a.getType)
      //  declareSort(tpe)

      //  val default: Expr = oDef.getOrElse(simplestValue(to))

      //  val arr = toSMT(RawArrayValue(Int32Type, elems.map {
      //    case (k, v) => IntLiteral(k) -> v
      //  }, default))

      //  FunctionApplication(constructors.toB(tpe), List(toSMT(size), arr))
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
        throw new Exception("Cannot build an array of negative length: " + size)
      } else if (size > 10) {
        val definedElements = elems.collect {
          case (IntLiteral(i), value) => (i, value)
        }
        finiteArray(definedElements, Some(default, IntLiteral(size)), baseType)

      } else {
        val entries = for (i <- 0 to size - 1) yield elems.getOrElse(IntLiteral(i), default)

        finiteArray(entries, None, baseType)
      }
    }

    override def transformExpr(e: Expr)(implicit binders: Map[Identifier, Identifier]): Option[Expr] = e match {
      case cc @ CaseClass(cct, args) if cct.classDef == ArrayCaseClass =>
        println("Hey there!")
        val Seq(rawArray, length) = args
        println(args)
        val leonArray = fromRaw(rawArray, length)
        println(leonArray)
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

