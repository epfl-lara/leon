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
import leon.purescala.DefOps
import leon.purescala.TypeOps
import leon.purescala.Extractors.Operator
import leon.evaluators.EvaluationResults

object StringEcoSystem {
  private def withIdentifier[T](name: String, tpe: TypeTree = Untyped)(f: Identifier => T): T = {
    val id = FreshIdentifier(name, tpe)
    f(id)
  }

  private def withIdentifiers[T](name: String, tpe: TypeTree, name2: String, tpe2: TypeTree = Untyped)(f: (Identifier, Identifier) => T): T = {
    withIdentifier(name, tpe)(id => withIdentifier(name2, tpe2)(id2 => f(id, id2)))
  }

  val StringList = new AbstractClassDef(FreshIdentifier("StringList"), Seq(), None)
  val StringListTyped = StringList.typed
  val StringCons = withIdentifiers("head", CharType, "tail", StringListTyped){ (head, tail) =>
    val d = new CaseClassDef(FreshIdentifier("StringCons"), Seq(), Some(StringListTyped), false)
    d.setFields(Seq(ValDef(head), ValDef(tail)))
    d
  }

  StringList.registerChild(StringCons)
  val StringConsTyped = StringCons.typed
  val StringNil  = new CaseClassDef(FreshIdentifier("StringNil"), Seq(), Some(StringListTyped), false)
  val StringNilTyped = StringNil.typed
  StringList.registerChild(StringNil)

  val StringSize = withIdentifiers("l", StringListTyped, "StringSize"){ (lengthArg, id) =>
    val fd = new FunDef(id, Seq(), Seq(ValDef(lengthArg)), IntegerType)
    fd.body = Some(withIdentifiers("h", CharType, "t", StringListTyped){ (h, t) =>
      MatchExpr(Variable(lengthArg), Seq(
        MatchCase(CaseClassPattern(None, StringNilTyped, Seq()), None, InfiniteIntegerLiteral(BigInt(0))),  
        MatchCase(CaseClassPattern(None, StringConsTyped, Seq(WildcardPattern(Some(h)), WildcardPattern(Some(t)))), None,
            Plus(InfiniteIntegerLiteral(BigInt(1)), FunctionInvocation(fd.typed, Seq(Variable(t)))))
      ))
    })
    fd
  }

  val StringListConcat = withIdentifiers("x", StringListTyped, "y", StringListTyped) { (x, y) =>
    val fd = new FunDef(FreshIdentifier("StringListConcat"), Seq(), Seq(ValDef(x), ValDef(y)), StringListTyped)
    fd.body = Some(
        withIdentifiers("h", CharType, "t", StringListTyped){ (h, t) =>
        MatchExpr(Variable(x), Seq(
          MatchCase(CaseClassPattern(None, StringNilTyped, Seq()), None, Variable(y)),
          MatchCase(CaseClassPattern(None, StringConsTyped, Seq(WildcardPattern(Some(h)), WildcardPattern(Some(t)))), None,
              CaseClass(StringConsTyped, Seq(Variable(h), FunctionInvocation(fd.typed, Seq(Variable(t), Variable(y)))))
          )))
        }
    )
    fd
  }

  val StringTake = withIdentifiers("tt", StringListTyped, "it", StringListTyped) { (tt, it) =>
    val fd = new FunDef(FreshIdentifier("StringTake"), Seq(), Seq(ValDef(tt), ValDef(it)), StringListTyped)
    fd.body = Some{
      withIdentifiers("h", CharType, "t", StringListTyped) { (h, t) =>
        withIdentifier("i", IntegerType){ i =>
        MatchExpr(Tuple(Seq(Variable(tt), Variable(it))), Seq(
          MatchCase(TuplePattern(None, Seq(CaseClassPattern(None, StringNilTyped, Seq()), WildcardPattern(None))), None,
              InfiniteIntegerLiteral(BigInt(0))),
          MatchCase(TuplePattern(None, Seq(CaseClassPattern(None, StringConsTyped, Seq(WildcardPattern(Some(h)), WildcardPattern(Some(t)))), WildcardPattern(Some(i)))), None,
              IfExpr(LessThan(Variable(i), InfiniteIntegerLiteral(BigInt(0))),
                  CaseClass(StringNilTyped, Seq()),
                  CaseClass(StringConsTyped, Seq(Variable(h),
                      FunctionInvocation(fd.typed, Seq(Variable(t), Minus(Variable(i), InfiniteIntegerLiteral(BigInt(1)))))))
          ))))
        }
      }
    }
    fd
  }

  val StringDrop = withIdentifiers("td", StringListTyped, "id", IntegerType) { (td, id) =>
    val fd = new FunDef(FreshIdentifier("StringDrop"), Seq(), Seq(ValDef(td), ValDef(id)), StringListTyped)
    fd.body = Some(
      withIdentifiers("h", CharType, "t", StringListTyped) { (h, t) =>
        withIdentifier("i", IntegerType){ i =>
      MatchExpr(Tuple(Seq(Variable(td), Variable(id))), Seq(
          MatchCase(TuplePattern(None, Seq(CaseClassPattern(None, StringNilTyped, Seq()), WildcardPattern(None))), None,
              InfiniteIntegerLiteral(BigInt(0))),
          MatchCase(TuplePattern(None, Seq(CaseClassPattern(None, StringConsTyped, Seq(WildcardPattern(Some(h)), WildcardPattern(Some(t)))), WildcardPattern(Some(i)))), None,
              IfExpr(LessThan(Variable(i), InfiniteIntegerLiteral(BigInt(0))),
                  CaseClass(StringConsTyped, Seq(Variable(h), Variable(t))),
                  FunctionInvocation(fd.typed, Seq(Variable(t), Minus(Variable(i), InfiniteIntegerLiteral(BigInt(1)))))
          ))))
      }}
    )
    fd
  }
  
  val StringSlice = withIdentifier("s", StringListTyped) { s => withIdentifiers("from", IntegerType, "to", IntegerType) { (from, to) =>
    val fd = new FunDef(FreshIdentifier("StringSlice"), Seq(), Seq(ValDef(s), ValDef(from), ValDef(to)), StringListTyped)
    fd.body = Some(
        FunctionInvocation(StringTake.typed,
            Seq(FunctionInvocation(StringDrop.typed, Seq(Variable(s), Variable(from))),
                Minus(Variable(to), Variable(from)))))
    fd
  } }
  
  val classDefs = Seq(StringList, StringCons, StringNil)
  val funDefs = Seq(StringSize, StringListConcat, StringTake, StringDrop, StringSlice)
}

object StringEncoder extends TheoryEncoder {
  import StringEcoSystem._

  private val stringBijection = new Bijection[String, Expr]()
  
  private def convertToString(e: Expr): String  = stringBijection.cachedA(e)(e match {
    case CaseClass(_, Seq(CharLiteral(c), l)) => c + convertToString(l)
    case CaseClass(_, Seq()) => ""
  })

  private def convertFromString(v: String): Expr = stringBijection.cachedB(v) {
    v.toList.foldRight(CaseClass(StringNilTyped, Seq())){
      case (char, l) => CaseClass(StringConsTyped, Seq(CharLiteral(char), l))
    }
  }

  val encoder = new Encoder {
    override def transform(e: Expr)(implicit binders: Map[Identifier, Identifier]): Expr = e match {
      case StringLiteral(v)          =>
        convertFromString(v)
      case StringLength(a)           =>
        FunctionInvocation(StringSize.typed, Seq(transform(a))).copiedFrom(e)
      case StringConcat(a, b)        =>
        FunctionInvocation(StringListConcat.typed, Seq(transform(a), transform(b))).copiedFrom(e)
      case SubString(a, start, Plus(start2, length)) if start == start2  =>
        FunctionInvocation(StringTake.typed, Seq(FunctionInvocation(StringDrop.typed, Seq(transform(a), transform(start))), transform(length))).copiedFrom(e)
      case SubString(a, start, end)  => 
        FunctionInvocation(StringSlice.typed, Seq(transform(a), transform(start), transform(end))).copiedFrom(e)
      case _ => super.transform(e)
    }

    override def transform(tpe: TypeTree): TypeTree = tpe match {
      case StringType => StringListTyped
      case _ => super.transform(tpe)
    }

    override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
      case LiteralPattern(binder, StringLiteral(s)) =>
        val newBinder = binder map transform
        val newPattern = s.foldRight(CaseClassPattern(None, StringNilTyped, Seq())) {
          case (elem, pattern) => CaseClassPattern(None, StringConsTyped, Seq(LiteralPattern(None, CharLiteral(elem)), pattern))
        }
        (newPattern.copy(binder = newBinder), (binder zip newBinder).filter(p => p._1 != p._2).toMap)
      case _ => super.transform(pat)
    }
  }

  val decoder = new Decoder {
    override def transform(e: Expr)(implicit binders: Map[Identifier, Identifier]): Expr = e match {
      case cc @ CaseClass(cct, args) if TypeOps.isSubtypeOf(cct, StringListTyped)=>
        StringLiteral(convertToString(cc)).copiedFrom(cc)
      case FunctionInvocation(StringSize, Seq(a)) =>
        StringLength(transform(a)).copiedFrom(e)
      case FunctionInvocation(StringListConcat, Seq(a, b)) =>
        StringConcat(transform(a), transform(b)).copiedFrom(e)
      case FunctionInvocation(StringTake, Seq(FunctionInvocation(StringDrop, Seq(a, start)), length)) =>
        val rstart = transform(start)
        SubString(transform(a), rstart, plus(rstart, transform(length))).copiedFrom(e)
      case _ => super.transform(e)
    }


    override def transform(tpe: TypeTree): TypeTree = tpe match {
      case StringListTyped | StringConsTyped | StringNilTyped => StringType
      case _ => super.transform(tpe)
    }

    override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = pat match {
      case CaseClassPattern(b, StringNilTyped, Seq()) =>
        val newBinder = b map transform
        (LiteralPattern(newBinder , StringLiteral("")), (b zip newBinder).filter(p => p._1 != p._2).toMap)

      case CaseClassPattern(b, StringConsTyped, Seq(LiteralPattern(_, CharLiteral(elem)), sub)) => transform(sub) match {
        case (LiteralPattern(_, StringLiteral(s)), binders) =>
          val newBinder = b map transform
          (LiteralPattern(newBinder, StringLiteral(elem + s)), (b zip newBinder).filter(p => p._1 != p._2).toMap ++ binders)
        case (e, binders) =>
          (LiteralPattern(None, StringLiteral("Failed to parse pattern back as string:" + e)), binders)
      }

      case _ => super.transform(pat)
    }
  }
}

