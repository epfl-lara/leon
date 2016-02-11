package leon
package solvers
package z3

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
  
  val StringList = AbstractClassDef(FreshIdentifier("StringList"), Seq(), None)
  val StringListTyped = StringList.typed
  val StringCons = withIdentifiers("head", CharType, "tail", StringListTyped){ (head, tail) =>
    val d = CaseClassDef(FreshIdentifier("StringCons"), Seq(), Some(StringListTyped), false)
    d.setFields(Seq(ValDef(head), ValDef(tail)))
    d
  }
  StringList.registerChild(StringCons)
  val StringConsTyped = StringCons.typed
  val StringNil  = CaseClassDef(FreshIdentifier("StringNil"), Seq(), Some(StringListTyped), false)
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

class Z3StringConversion(val p: Program) extends Z3StringConverters {
  val stringBijection = new Bijection[String, Expr]()
 
  import StringEcoSystem._
    
  lazy val listchar = StringList.typed
  lazy val conschar = StringCons.typed
  lazy val nilchar = StringNil.typed

  lazy val list_size = StringSize.typed
  lazy val list_++ = StringListConcat.typed
  lazy val list_take = StringTake.typed
  lazy val list_drop = StringDrop.typed
  lazy val list_slice = StringSlice.typed
  
  def getProgram = program_with_string_methods
  
  lazy val program_with_string_methods = {
    val p2 = DefOps.addClassDefs(p, StringEcoSystem.classDefs, p.library.Nil.get)
    DefOps.addFunDefs(p2, StringEcoSystem.funDefs, p2.library.escape.get)
  }

  def convertToString(e: Expr)(implicit p: Program): String  = 
    stringBijection.cachedA(e) {
      e match {
        case CaseClass(_, Seq(CharLiteral(c), l)) => c + convertToString(l)
        case CaseClass(_, Seq()) => ""
      }
    }
  def convertFromString(v: String): Expr =
    stringBijection.cachedB(v) {
      v.toList.foldRight(CaseClass(nilchar, Seq())){
        case (char, l) => CaseClass(conschar, Seq(CharLiteral(char), l))
      }
    }
}

trait Z3StringConverters  { self: Z3StringConversion =>
  import StringEcoSystem._
  val mappedVariables = new Bijection[Identifier, Identifier]()
    
  val globalFdMap = new Bijection[FunDef, FunDef]()
  
  trait BidirectionalConverters {
    def convertFunDef(fd: FunDef): FunDef
    def hasIdConversion(id: Identifier): Boolean
    def convertId(id: Identifier): Identifier
    def isTypeToConvert(tpe: TypeTree): Boolean
    def convertType(tpe: TypeTree): TypeTree
    def convertPattern(pattern: Pattern): Pattern
    def convertExpr(expr: Expr)(implicit bindings: Map[Identifier, Expr]): Expr
    
    object PatternConverted {
      def unapply(e: Pattern): Option[Pattern] = Some(e match {
        case InstanceOfPattern(binder, ct) =>
          InstanceOfPattern(binder.map(convertId), convertType(ct).asInstanceOf[ClassType])
        case WildcardPattern(binder) =>
          WildcardPattern(binder.map(convertId))
        case CaseClassPattern(binder, ct, subpatterns) =>
          CaseClassPattern(binder.map(convertId), convertType(ct).asInstanceOf[CaseClassType], subpatterns map convertPattern)
        case TuplePattern(binder, subpatterns) =>
          TuplePattern(binder.map(convertId), subpatterns map convertPattern)
        case UnapplyPattern(binder, TypedFunDef(fd, tpes), subpatterns) =>
          UnapplyPattern(binder.map(convertId), TypedFunDef(convertFunDef(fd), tpes map convertType), subpatterns map convertPattern)
        case PatternExtractor(es, builder) =>
          builder(es map convertPattern)
      })
    }
    
    object ExprConverted {
      def unapply(e: Expr)(implicit bindings: Map[Identifier, Expr]): Option[Expr] = Some(e match {
        case Variable(id) if bindings contains id => bindings(id).copiedFrom(e)
        case Variable(id) if hasIdConversion(id) => Variable(convertId(id)).copiedFrom(e)
        case Variable(id) => e
        case pl@PartialLambda(mappings, default, tpe) =>
          PartialLambda(
              mappings.map(kv => (kv._1.map(argtpe => convertExpr(argtpe)),
                  convertExpr(kv._2))),
                  default.map(d => convertExpr(d)), convertType(tpe).asInstanceOf[FunctionType])
        case Lambda(args, body) =>
          val new_bindings = scala.collection.mutable.ListBuffer[(Identifier, Identifier)]()
          for(arg <- args) {
            val in = arg.getType
            if(convertType(in) ne in) {
              new_bindings += (arg.id -> convertId(arg.id))
            }
          }
          val new_args = new_bindings.map(x => ValDef(x._2))
          Lambda(new_args,
              convertExpr(body)(bindings ++ new_bindings.map(t => (t._1, Variable(t._2))))).copiedFrom(e)
        case Let(a, expr, body) if isTypeToConvert(a.getType) => 
          val new_a = convertId(a)
          val new_bindings = bindings + (a -> Variable(new_a))
          val expr2 = convertExpr(expr)(new_bindings)
          val body2 = convertExpr(body)(new_bindings)
          Let(new_a, expr2, body2).copiedFrom(e)
        case CaseClass(CaseClassType(ccd, tpes), args) =>
          CaseClass(CaseClassType(ccd, tpes map convertType), args map convertExpr).copiedFrom(e)
        case CaseClassSelector(CaseClassType(ccd, tpes), caseClass, selector) =>
          CaseClassSelector(CaseClassType(ccd, tpes map convertType), convertExpr(caseClass), selector).copiedFrom(e)
        case MethodInvocation(rec: Expr, cd: ClassDef, TypedFunDef(fd, tpes), args: Seq[Expr]) => 
          MethodInvocation(convertExpr(rec), cd, TypedFunDef(convertFunDef(fd), tpes map convertType), args map convertExpr).copiedFrom(e)
        case FunctionInvocation(TypedFunDef(fd, tpes), args) =>
          FunctionInvocation(TypedFunDef(convertFunDef(fd), tpes map convertType), args map convertExpr).copiedFrom(e)
        case This(ct: ClassType) =>
          This(convertType(ct).asInstanceOf[ClassType]).copiedFrom(e)
        case IsInstanceOf(expr, ct) =>
          IsInstanceOf(convertExpr(expr), convertType(ct).asInstanceOf[ClassType]).copiedFrom(e)
        case AsInstanceOf(expr, ct) => 
          AsInstanceOf(convertExpr(expr), convertType(ct).asInstanceOf[ClassType]).copiedFrom(e)
        case Tuple(args) =>
          Tuple(for(arg <- args) yield convertExpr(arg)).copiedFrom(e)
        case MatchExpr(scrutinee, cases) =>
          MatchExpr(convertExpr(scrutinee), for(MatchCase(pattern, guard, rhs) <- cases) yield {
            MatchCase(convertPattern(pattern), guard.map(convertExpr), convertExpr(rhs))
          })
        case Operator(es, builder) =>
          val rec = convertExpr _
          val newEs = es.map(rec)
          if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
            builder(newEs).copiedFrom(e)
          } else {
            e
          }
        case e => e
      })
    }
    
    def convertModel(model: Model): Model = {
      new Model(model.ids.map{i =>
        val id = convertId(i)
        id -> convertExpr(model(i))(Map())
      }.toMap)
    }
    
    def convertResult(result: EvaluationResults.Result[Expr]) = {
      result match {
        case EvaluationResults.Successful(e) => EvaluationResults.Successful(convertExpr(e)(Map()))
        case result => result
      }
    }
  }
  
  object Forward extends BidirectionalConverters {
    /* The conversion between functions should already have taken place */
    def convertFunDef(fd: FunDef): FunDef = {
      globalFdMap.getBorElse(fd, fd)
    }
    def hasIdConversion(id: Identifier): Boolean = {
      mappedVariables.containsA(id)
    }
    def convertId(id: Identifier): Identifier = {
      mappedVariables.getB(id) match {
        case Some(idB) => idB
        case None =>
          if(isTypeToConvert(id.getType)) {
            val new_id = FreshIdentifier(id.name, convertType(id.getType))
            mappedVariables += (id -> new_id)
            new_id
          } else id
      }
    }
    def isTypeToConvert(tpe: TypeTree): Boolean = 
      TypeOps.exists(StringType == _)(tpe)
    def convertType(tpe: TypeTree): TypeTree =
      TypeOps.preMap{ case StringType => Some(StringList.typed) case e => None}(tpe)
    def convertPattern(e: Pattern): Pattern = e match {
      case LiteralPattern(binder, StringLiteral(s)) =>
        s.foldRight(CaseClassPattern(None, StringNilTyped, Seq())) {
          case (elem, pattern) =>
            CaseClassPattern(None, StringConsTyped, Seq(LiteralPattern(None, CharLiteral(elem)), pattern))
        }
      case PatternConverted(e) => e
    }
    
    /** Method which can use recursively StringConverted in its body in unapply positions */
    def convertExpr(e: Expr)(implicit bindings: Map[Identifier, Expr]): Expr = e match {
      case Variable(id) if isTypeToConvert(id.getType) => Variable(convertId(id)).copiedFrom(e)
      case StringLiteral(v)          =>
        // No string support for z3 at this moment.
        val stringEncoding = convertFromString(v)
        convertExpr(stringEncoding).copiedFrom(e)
      case StringLength(a)           =>
        FunctionInvocation(list_size, Seq(convertExpr(a))).copiedFrom(e)
      case StringConcat(a, b)        =>
        FunctionInvocation(list_++, Seq(convertExpr(a), convertExpr(b))).copiedFrom(e)
      case SubString(a, start, Plus(start2, length)) if start == start2  =>
        FunctionInvocation(list_take,
          Seq(FunctionInvocation(list_drop, Seq(convertExpr(a), convertExpr(start))), convertExpr(length))).copiedFrom(e)
      case SubString(a, start, end)  => 
        FunctionInvocation(list_slice, Seq(convertExpr(a), convertExpr(start), convertExpr(end))).copiedFrom(e)
      case MatchExpr(scrutinee, cases) =>
        MatchExpr(convertExpr(scrutinee), for(MatchCase(pattern, guard, rhs) <- cases) yield {
          MatchCase(convertPattern(pattern), guard.map(convertExpr), convertExpr(rhs))
        }) 
      case ExprConverted(e) => e
    }
  }
  
  object Backward extends BidirectionalConverters {
    def convertFunDef(fd: FunDef): FunDef = {
      globalFdMap.getAorElse(fd, fd)
    }
    def hasIdConversion(id: Identifier): Boolean = {
      mappedVariables.containsB(id)
    }
    def convertId(id: Identifier): Identifier = {
      mappedVariables.getA(id) match {
        case Some(idA) => idA
        case None =>
          if(isTypeToConvert(id.getType)) {
            val old_type = convertType(id.getType)
            val old_id = FreshIdentifier(id.name, old_type)
            mappedVariables += (old_id -> id)
            old_id
          } else id
      }
    }
    def convertIdToMapping(id: Identifier): (Identifier, Variable) = {
      id -> Variable(convertId(id))
    }
    def isTypeToConvert(tpe: TypeTree): Boolean = 
      TypeOps.exists(t => TypeOps.isSubtypeOf(t, StringListTyped))(tpe)
    def convertType(tpe: TypeTree): TypeTree = {
      TypeOps.preMap{
        case StringList | StringCons | StringNil => Some(StringType)
        case e => None}(tpe)
    }
    def convertPattern(e: Pattern): Pattern = e match {
    case CaseClassPattern(b, StringNilTyped, Seq()) =>
      LiteralPattern(b.map(convertId), StringLiteral(""))
    case CaseClassPattern(b, StringConsTyped, Seq(LiteralPattern(_, CharLiteral(elem)), subpattern)) =>
      convertPattern(subpattern) match {
        case LiteralPattern(_, StringLiteral(s))
         => LiteralPattern(b.map(convertId), StringLiteral(elem + s))
        case e => LiteralPattern(None, StringLiteral("Failed to parse pattern back as string:" + e))
      }
    case PatternConverted(e) => e
  }
    
  
  
  def convertExpr(e: Expr)(implicit bindings: Map[Identifier, Expr]): Expr = 
    e match {
      case cc@CaseClass(cct, args) if TypeOps.isSubtypeOf(cct, StringListTyped)=>
        StringLiteral(convertToString(cc)(self.p))
      case FunctionInvocation(StringSize, Seq(a)) =>
        StringLength(convertExpr(a)).copiedFrom(e)
      case FunctionInvocation(StringListConcat, Seq(a, b))      =>
        StringConcat(convertExpr(a), convertExpr(b)).copiedFrom(e)
      case FunctionInvocation(StringTake,
            Seq(FunctionInvocation(StringDrop, Seq(a, start)), length)) =>
        val rstart = convertExpr(start)
        SubString(convertExpr(a), rstart, plus(rstart, convertExpr(length))).copiedFrom(e)
      case ExprConverted(e) => e
    }
  }
}