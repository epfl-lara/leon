
package leon
package verification
package theorem

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._

/** This class provides encoding and decoding facilities for leon.theorem classes.
  *
  * Encoding takes a PureScala expression and returns the corresponding
  * encoded Term that can be manipulated by users.
  *
  * Conversly, decoding takes an encoded Term and returns the corresponding
  * PureScala expression.
  */
class ExprEncoder(vctx: VerificationContext) {

  val library = Library(vctx.program)
  val leonLib = leon.utils.Library(vctx.program)

  /** Encodes an expression as a leon.theorem.Term.
    *
    * @param expr The expression to encode.
    * @param env  A mapping between PureScala identifiers and leon.theorem.Identifier.
    */
  def encodeExpr(expr: Expr, env: Map[Identifier, Expr]): Expr = expr match {
    case NoTree(_) | Error(_, _) => ???
    case Require(pred, body) => ???
    case Ensuring(body, pred) => ???
    case Assert(pred, error, body) => ???
    case Variable(identifier) => caseClass(library.Variable, env(identifier))
    case Let(binder, value, body) => {
      val v = encodeExpr(value, env)
      val fresh = identifier(binder.uniqueName)
      val b = encodeExpr(body, env.updated(binder, fresh))
      caseClass(library.Let, fresh, v, b)
    }
    case LetDef(fds, body) => ???
    case MethodInvocation(rec, cd, tfd, args) => ???
    case This(ct) => ???
    case Application(callee, args) => ???
    case Lambda(args, body) => ???
    case FiniteLambda(mapping, default, tpe) => ???
    case Forall(args, body) => {
      val newEnv = args.map {
        (vd: ValDef) => vd.id -> identifier(vd.id.uniqueName)
      }

      val encodedBody = encodeExpr(body, env ++ newEnv)
      newEnv.foldRight(encodedBody) {
        (x: (Identifier, Expr), xs: Expr) => caseClass(library.Forall, 
          x._2, 
          StringLiteral(encodeType(x._1.getType)), 
          xs)
      }
    }
    case FunctionInvocation(tfd, args) => {
      val funName = tfd.fd.qualifiedName(vctx.program)
      caseClass(library.FunctionInvocation, 
        StringLiteral(funName),
        encodeList(args.map(encodeExpr(_, env))))
    }
    case IfExpr(cond, thenn, elze) => ???
    case MatchExpr(scrutinee, cases) => ???
    case Passes(in, out, cases) => ???
    case v@CharLiteral(_) => caseClass(library.CharLiteral, v) 
    case v@IntLiteral(_) => caseClass(library.IntLiteral, v)
    case v@InfiniteIntegerLiteral(_) => caseClass(library.BigIntLiteral, v)
    case FractionalLiteral(numerator, denominator) => ???
    case v@StringLiteral(_) => caseClass(library.StringLiteral, v)
    case v@BooleanLiteral(_) => caseClass(library.BooleanLiteral, v)
    case UnitLiteral() => caseClass(library.UnitLiteral)
    case GenericValue(tp, id) => ???
    case CaseClass(ct, args) => ???
    case IsInstanceOf(expr, classType) => ???
    case AsInstanceOf(expr, tpe) => ???
    case CaseClassSelector(classType, caseClass, selector) => ???
    case Equals(left, right) => caseClass(library.Equals,
      encodeExpr(left, env),
      encodeExpr(right, env))
    case And(exprs) => reduce(library.And, exprs.map(encodeExpr(_, env)))
    case Or(exprs) => reduce(library.Or, exprs.map(encodeExpr(_, env)))
    case Implies(left, right) => caseClass(library.Implies,
      encodeExpr(left, env),
      encodeExpr(right, env))
    case Not(expr) => caseClass(library.Not, encodeExpr(expr, env))
    case StringConcat(lhs, rhs) => ???
    case SubString(expr, start, end) => ???
    case BigSubString(expr, start, end) => ???
    case StringLength(expr) => ???
    case StringBigLength(expr) => ???
    case Plus(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("+"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case Minus(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("-"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case UMinus(expr) => ???
    case Times(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("*"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case Division(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("/"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case Remainder(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("%"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case Modulo(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("mod"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case LessThan(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("<"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case GreaterThan(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral(">"),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case LessEquals(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("<="),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case GreaterEquals(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral(">="),
      encodeExpr(lhs, env),
      encodeExpr(rhs, env))
    case BVPlus(lhs, rhs) => ???
    case BVMinus(lhs, rhs) => ???
    case BVUMinus(expr) => ???
    case BVTimes(lhs, rhs) => ???
    case BVDivision(lhs, rhs) => ???
    case BVRemainder(lhs, rhs) => ???
    case BVNot(expr) => ???
    case BVAnd(lhs, rhs) => ???
    case BVOr(lhs, rhs) => ???
    case BVShiftLeft(lhs, rhs) => ???
    case BVAShiftRight(lhs, rhs) => ???
    case BVLShiftRight(lhs, rhs) => ???
    case RealPlus(lhs, rhs) => ???
    case RealMinus(lhs, rhs) => ???
    case RealUMinus(expr) => ???
    case RealTimes(lhs, rhs) => ???
    case RealDivision(lhs, rhs) => ???
    case Tuple(exprs) => ???
    case TupleSelect(tuple, index) => ???
    case FiniteSet(elements, base) => ???
    case SetAdd(set, elem) => ???
    case ElementOfSet(element, set) => ???
    case SetCardinality(set) => ???
    case SetIntersection(set1, set2) => ???
    case SetUnion(set1, set2) => ???
    case SetDifference(set1, set2) => ???
    case FiniteBag(elements, base) => ???
    case MultiplicityInBag(element, bag) => ???
    case BagIntersection(set1, set2) => ???
    case BagUnion(set1, set2) => ???
    case BagDifference(set1, set2) => ???
    case FiniteMap(pairs, keyType, valueType) => ???
    case MapApply(map, key) => ???
    case MapUnion(map1, map2) => ???
    case MapDifference(map, keys) => ???
    case ArraySelect(array, index) => ???
    case ArrayUpdated(array, index, newValue) => ???
    case ArrayLength(array) => ???
    case NonemptyArray(elems, defaultLength) => ???
    case EmptyArray(tpe) => ???
    case Choose(pred) => ???
    case WithOracle(oracles, body) => ???
    case Hole(tpe, alts) => ???
    case _ => throw new Exception("Unsupported expression.")
  }

  /** Encodes a type as a String. */
  private def encodeType(tpe: TypeTree): String = tpe match {
    // TODO: Complete this.
    case BooleanType => "Boolean"
    case UnitType => "Unit"
    case CharType => "Char"
    case IntegerType => "BigInt"
    case Int32Type => "Int"
    case StringType => "String"
    case AbstractClassType(cd, Seq()) => cd.id.name
    case AbstractClassType(cd, tps) => cd.id.name + tps.map(encodeType _).mkString("[", ", ", "]")
    case CaseClassType(cd, Seq()) => cd.id.name
    case CaseClassType(cd, tps) => cd.id.name + tps.map(encodeType _).mkString("[", ", ", "]")
  }

  /** Decodes a type from a String. */
  private def decodeType(tpe: String): TypeTree = tpe match {
    // TODO: Complete this.
    case "Boolean" => BooleanType
    case "Unit" => UnitType
    case "Char" => CharType
    case "BigInt" => IntegerType
    case "Int" => Int32Type
    case "String" => StringType
  }

  /** Encodes a sequence of encoded Term's as a leon List.
    *
    * This function does NOT encode the expressions themselves,
    * and thus must be encoded beforehand.
    */ 
  private def encodeList(exprs: Seq[Expr]): Expr = {
    val nil: Expr = CaseClass(
      CaseClassType(leonLib.Nil.get, Seq(AbstractClassType(library.Term.get, Seq()))),
      Seq())
    def cons(x: Expr, xs: Expr): Expr = CaseClass(
      CaseClassType(leonLib.Cons.get, Seq(AbstractClassType(library.Term.get, Seq()))),
      Seq(x, xs))

    exprs.foldRight(nil)(cons _)
  }

  /** Decodes a leon List to a proper sequence of Expr.
    *
    * This function does NOT decode the elements of the List.
    */
  private def decodeList(expr: Expr): Seq[Expr] = expr match {
    case CaseClass(ct, Seq(x, xs)) if (ct.classDef == leonLib.Cons.get) => x +: decodeList(xs)
    case CaseClass(ct, Seq()) if (ct.classDef == leonLib.Nil.get) => Seq()
  }

  /** Creates a leon.theorem.Identifier with the given name. */
  def identifier(name: String): Expr = caseClass(library.Identifier, StringLiteral(name))

  /** Creates a case class of the given CaseClassDef. */
  def caseClass(cc: Option[CaseClassDef], args: Expr*): Expr =
    CaseClass(CaseClassType(cc.get, Seq()), args.toSeq)

  
  /** Fold the sequence of arguments using the given case class.
    *
    * The number of arguments must be at least 2.
    */
  private def reduce(cc: Option[CaseClassDef], args: Seq[Expr]): Expr = {
    require(args.size >= 2)

    if (args.size == 2) {
      caseClass(cc, args : _*)
    }
    else {
      caseClass(cc, args.head, reduce(cc, args.tail))
    }
  }

  /** Decodes an encoded Term to its equivalent PureScala expression.
    *
    * @param expr An evaluated expression of type leon.theorem.Term.
    * @param env  A mapping between expressions of type leon.theorem.Identifier
    *             and PureScala Identifier's.
    */
  def decodeExpr(expr: Expr, env: Map[Expr, Identifier]): Expr = expr match {
    // Operators
    case CaseClass(ct, Seq(op, lhs, rhs)) if (ct.classDef == library.BinOp.get) => op match {
      case StringLiteral("+") => Plus(decodeExpr(lhs, env), decodeExpr(rhs, env))
      case StringLiteral(">=") => GreaterEquals(decodeExpr(lhs, env), decodeExpr(rhs, env))
    }
    // Literals
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.BigIntLiteral.get) => v
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.IntLiteral.get) => v
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.BooleanLiteral.get) => v
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.StringLiteral.get) => v
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.CharLiteral.get) => v
    case CaseClass(ct, Seq()) if (ct.classDef == library.UnitLiteral.get) => UnitLiteral()
    // Bindings
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.Variable.get) => Variable(env(v))
    case CaseClass(ct, Seq(i, v, b)) if (ct.classDef == library.Let.get) => {
      val CaseClass(_, Seq(StringLiteral(s))) = i
      val pv = decodeExpr(v, env)
      val freshId = FreshIdentifier(s, pv.getType, true)
      val pb = decodeExpr(b, env.updated(i, freshId))
      let(freshId, pv, pb)
    }
    // Quantifiers
    case CaseClass(ct, Seq(i, t, b)) if (ct.classDef == library.Forall.get) => {
      val CaseClass(_, Seq(StringLiteral(s))) = i
      val StringLiteral(tpe) = t
      val freshId = FreshIdentifier(s, decodeType(tpe), true)  // TODO: Infer the type?
      val pb = decodeExpr(b, env.updated(i, freshId))
      Forall(Seq(ValDef(freshId)), pb)
    }
    // Invocations
    case CaseClass(ct, Seq(StringLiteral(name), args)) if (ct.classDef == library.FunctionInvocation.get) => {
      vctx.program.lookupFunDef(name) match {
        case None => {
          vctx.reporter.fatalError("Function not found: " + name)
        }
        case Some(fd) => {
          val decodedList = decodeList(args)
          val decodedArgs = decodedList.map(decodeExpr(_, env))
          fd.applied(decodedArgs)
        }
      }
    }
    // Boolean operators
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.Not.get) => Not(decodeExpr(v, env))
    case CaseClass(ct, Seq(v, w)) if (ct.classDef == library.Implies.get) => Implies(decodeExpr(v, env), decodeExpr(w, env))
    case CaseClass(ct, Seq(v, w)) if (ct.classDef == library.And.get) => And(decodeExpr(v, env), decodeExpr(w, env))
    case CaseClass(ct, Seq(v, w)) if (ct.classDef == library.Or.get) => Or(decodeExpr(v, env), decodeExpr(w, env))
    case CaseClass(ct, Seq(v, w)) if (ct.classDef == library.Iff.get) => {
      // Use equals?
      val a = decodeExpr(v, env)
      val b = decodeExpr(w, env)

      And(Implies(a, b), Implies(b, a))
    }
    case CaseClass(ct, Seq(v, w)) if (ct.classDef == library.Equals.get) => Equals(decodeExpr(v, env), decodeExpr(w, env))
    case _ => throw new Exception("Unsupported expression.")
  }
}