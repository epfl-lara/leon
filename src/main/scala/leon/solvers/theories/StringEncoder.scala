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

class StringEncoder(ctx: LeonContext, p: Program) extends TheoryEncoder {
  val String     = p.library.lookupUnique[ClassDef]("leon.theories.String").typed
  val StringCons = p.library.lookupUnique[CaseClassDef]("leon.theories.StringCons").typed
  val StringNil  = p.library.lookupUnique[CaseClassDef]("leon.theories.StringNil").typed

  val Size   = p.library.lookupUnique[FunDef]("leon.theories.String.size").typed
  val Take   = p.library.lookupUnique[FunDef]("leon.theories.String.take").typed
  val Drop   = p.library.lookupUnique[FunDef]("leon.theories.String.drop").typed
  val Slice  = p.library.lookupUnique[FunDef]("leon.theories.String.slice").typed
  val Concat = p.library.lookupUnique[FunDef]("leon.theories.String.concat").typed

  private val stringBijection = new Bijection[String, Expr]()
  
  private def convertToString(e: Expr): String  = stringBijection.cachedA(e)(e match {
    case CaseClass(_, Seq(CharLiteral(c), l)) => c + convertToString(l)
    case CaseClass(_, Seq()) => ""
  })

  private def convertFromString(v: String): Expr = stringBijection.cachedB(v) {
    v.toList.foldRight(CaseClass(StringNil, Seq())){
      case (char, l) => CaseClass(StringCons, Seq(CharLiteral(char), l))
    }
  }

  val encoder = new Encoder {
    override def transform(e: Expr)(implicit binders: Map[Identifier, Identifier]): Expr = e match {
      case StringLiteral(v)          =>
        convertFromString(v)
      case StringLength(a)           =>
        FunctionInvocation(Size, Seq(transform(a))).copiedFrom(e)
      case StringConcat(a, b)        =>
        FunctionInvocation(Concat, Seq(transform(a), transform(b))).copiedFrom(e)
      case SubString(a, start, Plus(start2, length)) if start == start2  =>
        FunctionInvocation(Take, Seq(FunctionInvocation(Drop, Seq(transform(a), transform(start))), transform(length))).copiedFrom(e)
      case SubString(a, start, end)  => 
        FunctionInvocation(Slice, Seq(transform(a), transform(start), transform(end))).copiedFrom(e)
      case _ => super.transform(e)
    }

    override def transform(tpe: TypeTree): TypeTree = tpe match {
      case StringType => String
      case _ => super.transform(tpe)
    }

    override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
      case LiteralPattern(binder, StringLiteral(s)) =>
        val newBinder = binder map transform
        val newPattern = s.foldRight(CaseClassPattern(None, StringNil, Seq())) {
          case (elem, pattern) => CaseClassPattern(None, StringCons, Seq(LiteralPattern(None, CharLiteral(elem)), pattern))
        }
        (newPattern.copy(binder = newBinder), (binder zip newBinder).filter(p => p._1 != p._2).toMap)
      case _ => super.transform(pat)
    }
  }

  val decoder = new Decoder {
    override def transform(e: Expr)(implicit binders: Map[Identifier, Identifier]): Expr = e match {
      case cc @ CaseClass(cct, args) if TypeOps.isSubtypeOf(cct, String)=>
        StringLiteral(convertToString(cc)).copiedFrom(cc)
      case FunctionInvocation(Size, Seq(a)) =>
        StringLength(transform(a)).copiedFrom(e)
      case FunctionInvocation(Concat, Seq(a, b)) =>
        StringConcat(transform(a), transform(b)).copiedFrom(e)
      case FunctionInvocation(Slice, Seq(a, from, to)) =>
        SubString(transform(a), transform(from), transform(to)).copiedFrom(e)
      case FunctionInvocation(Take, Seq(FunctionInvocation(Drop, Seq(a, start)), length)) =>
        val rstart = transform(start)
        SubString(transform(a), rstart, plus(rstart, transform(length))).copiedFrom(e)
      case FunctionInvocation(Take, Seq(a, length)) =>
        SubString(transform(a), InfiniteIntegerLiteral(0), transform(length)).copiedFrom(e)
      case FunctionInvocation(Drop, Seq(a, count)) =>
        val ra = transform(a)
        SubString(ra, transform(count), StringLength(ra)).copiedFrom(e)
      case _ => super.transform(e)
    }


    override def transform(tpe: TypeTree): TypeTree = tpe match {
      case String | StringCons | StringNil => StringType
      case _ => super.transform(tpe)
    }

    override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
      case CaseClassPattern(b, StringNil, Seq()) =>
        val newBinder = b map transform
        (LiteralPattern(newBinder , StringLiteral("")), (b zip newBinder).filter(p => p._1 != p._2).toMap)

      case CaseClassPattern(b, StringCons, Seq(LiteralPattern(_, CharLiteral(elem)), sub)) => transform(sub) match {
        case (LiteralPattern(_, StringLiteral(s)), binders) =>
          val newBinder = b map transform
          (LiteralPattern(newBinder, StringLiteral(elem + s)), (b zip newBinder).filter(p => p._1 != p._2).toMap ++ binders)
        case (e, binders) =>
          throw new Unsupported(pat, "Failed to parse pattern back as string: " + e)(ctx)
      }

      case _ => super.transform(pat)
    }
  }
}

