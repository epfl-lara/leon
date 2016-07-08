
package leon
package verification

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Types._
import theorem.Library

class TermConverter(vctx: VerificationContext) {

  val library = Library(vctx.program)
  
  def fromPureScala(expr: Expr, env: Map[Identifier, Expr]): Expr = expr match {
    case NoTree(_) | Error(_, _) => ???
    case Require(pred, body) => ???
    case Ensuring(body, pred) => ???
    case Assert(pred, error, body) => ???
    case Variable(identifier) => caseClass(library.Variable, env(identifier))
    case Let(binder, value, body) => {
      val v = fromPureScala(value, env)
      val fresh = makeIdentifier("fresh")
      val b = fromPureScala(body, env.updated(binder, fresh))
      caseClass(library.Let, fresh, v, b)
    }
    case LetDef(fds, body) => ???
    case MethodInvocation(rec, cd, tfd, args) => ???
    case This(ct) => ???
    case Application(callee, args) => ???
    case Lambda(args, body) => ???
    case FiniteLambda(mapping, default, tpe) => ???
    case Forall(args, body) => ???
    case FunctionInvocation(tfd, args) => ???
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
      fromPureScala(left, env),
      fromPureScala(right, env))
    case And(exprs) => fold(library.And, exprs)
    case Or(exprs) => fold(library.Or, exprs)
    case Implies(left, right) => caseClass(library.Implies,
      fromPureScala(left, env),
      fromPureScala(right, env))
    case Not(expr) => caseClass(library.Not, fromPureScala(expr, env))
    case StringConcat(lhs, rhs) => ???
    case SubString(expr, start, end) => ???
    case BigSubString(expr, start, end) => ???
    case StringLength(expr) => ???
    case StringBigLength(expr) => ???
    case Plus(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("+"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case Minus(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("-"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case UMinus(expr) => ???
    case Times(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("*"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case Division(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("/"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case Remainder(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("%"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case Modulo(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("mod"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case LessThan(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("<"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case GreaterThan(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral(">"),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case LessEquals(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral("<="),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
    case GreaterEquals(lhs, rhs) => caseClass(library.BinOp,
      StringLiteral(">="),
      fromPureScala(lhs, env),
      fromPureScala(rhs, env))
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

  def makeIdentifier(name: String): Expr = caseClass(library.Identifier, StringLiteral(name))

  def caseClass(cc: Option[CaseClassDef], args: Expr*) =
    CaseClass(CaseClassType(cc.get, Seq()), args.toSeq)

  def fold(cc: Option[CaseClassDef], args: Seq[Expr]): Expr = {
    require(args.size >= 2)

    if (args.size == 2) {
      caseClass(cc, args : _*)
    }
    else {
      caseClass(cc, args.head, fold(cc, args.tail))
    }
  }

  def toPureScala(expr: Expr, env: Map[Expr, Identifier]): Expr = expr match {
    case CaseClass(ct, Seq(op, lhs, rhs)) if (ct.classDef == library.BinOp.get) => op match {
      case StringLiteral("+") => Plus(toPureScala(lhs, env), toPureScala(rhs, env))
      case StringLiteral(">=") => GreaterEquals(toPureScala(lhs, env), toPureScala(rhs, env))
    }
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.BigIntLiteral.get) => v
    case CaseClass(ct, Seq(v)) if (ct.classDef == library.Variable.get) => Variable(env(v))
    case _ => throw new Exception("Unsupported expression.")
  }
}