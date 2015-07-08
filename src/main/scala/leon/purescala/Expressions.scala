/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Types._
import TypeOps._
import Definitions._
import Extractors._
import Constructors._
import ExprOps.replaceFromIDs

/** Expression definitions for Pure Scala. */
object Expressions {

  private def checkParamTypes(real: Seq[Typed], formal: Seq[Typed], result: TypeTree): TypeTree = {
    if (real zip formal forall { case (real, formal) => isSubtypeOf(real.getType, formal.getType)} ) {
      result.unveilUntyped
    } else {
      //println(real map { r => s"$r: ${r.getType}"} mkString ", " )
      //println(formal map { r => s"$r: ${r.getType}" } mkString ", " )
      Untyped
    }
  }

  abstract class Expr extends Tree with Typed {
    def untyped = {
      //println("@" + this.getPos)
      //println(this)
      //println
      Untyped
    }
  }

  trait Terminal {
    self: Expr =>
  }


  /* Stands for an undefined Expr, similar to ??? or null */
  case class NoTree(tpe: TypeTree) extends Expr with Terminal {
    val getType = tpe
  }


  /* Specifications */

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(tpe: TypeTree, description: String) extends Expr with Terminal {
    val getType = tpe
  }

  // Preconditions
  case class Require(pred: Expr, body: Expr) extends Expr {
    val getType = {
      if (pred.getType == BooleanType)
        body.getType
      else untyped
    }
  }

  // Postconditions
  case class Ensuring(body: Expr, pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType) if isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        untyped
    }
    def toAssert: Expr = {
      val res = FreshIdentifier("res", getType, true)
      Let(res, body, Assert(
        application(pred, Seq(Variable(res))),
        Some("Postcondition failed @" + this.getPos), Variable(res)
      ))
    }
  }

  // Local assertions
  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    val getType = {
      if (pred.getType == BooleanType)
        body.getType
      else untyped
    }
  }


  /* Variables */
  case class Variable(id: Identifier) extends Expr with Terminal {
    val getType = id.getType
  }


  /* Local val's and def's */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val getType = {
      // We can't demand anything sticter here, because some binders are
      // typed context-wise
      if (typesCompatible(value.getType, binder.getType))
        body.getType
      else {
        untyped
      }
    }
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    val getType = body.getType
  }


  /**
   * OO Trees
   *
   * Both MethodInvocation and This get removed by phase MethodLifting. Methods become functions,
   * This becomes first argument, and MethodInvocation becomes FunctionInvocation.
   */
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    val getType = {
      // We need ot instantiate the type based on the type of the function as well as receiver
      val fdret = tfd.returnType
      val extraMap: Map[TypeParameterDef, TypeTree] = rec.getType match {
        case ct: ClassType =>
          (cd.tparams zip ct.tps).toMap
        case _ =>
          Map()
      }
      instantiateType(fdret, extraMap)
    }
  }

  case class This(ct: ClassType) extends Expr with Terminal {
    val getType = ct
  }


  /* HOFs */
  case class Application(callee: Expr, args: Seq[Expr]) extends Expr {
    val getType = callee.getType match {
      case FunctionType(from, to) =>
        checkParamTypes(args, from, to)
      case _ =>
        untyped
    }
  }

  case class Lambda(args: Seq[ValDef], body: Expr) extends Expr {
    val getType = FunctionType(args.map(_.getType), body.getType).unveilUntyped
    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == args.size)
      (args map { _.id } zip realArgs).toMap
    }
    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      replaceFromIDs(paramSubst(realArgs), e)
    }
  }


  /* Control flow */
  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    require(tfd.params.size == args.size)
    val getType = checkParamTypes(args, tfd.params, tfd.returnType)
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(untyped).unveilUntyped
  }

  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)
    val getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(untyped).unveilUntyped
  }

  case class MatchCase(pattern : Pattern, optGuard : Option[Expr], rhs: Expr) extends Tree {
    def expressions: Seq[Expr] = optGuard.toList :+ rhs
  }

  sealed abstract class Pattern extends Tree {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.flatMap(_.binders).toSet
    def binders: Set[Identifier] = subBinders ++ binder.toSet

    def withBinder(b : Identifier) = { this match {
      case Pattern(None, subs, builder) => builder(Some(b), subs)
      case other => other
    }}.copiedFrom(this)
  }

  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern { // c: Class
    val subPatterns = Seq()
  }
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq()
  } 
  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern

  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern

  case class LiteralPattern[+T](binder: Option[Identifier], lit : Literal[T]) extends Pattern {
    val subPatterns = Seq()    
  }

  case class UnapplyPattern(binder: Option[Identifier], unapplyFun: TypedFunDef, subPatterns: Seq[Pattern]) extends Pattern {
    // Hacky, but ok
    lazy val optionType = unapplyFun.returnType.asInstanceOf[AbstractClassType]
    lazy val Seq(noneType, someType) = optionType.knownCCDescendants.sortBy(_.fields.size)
    lazy val someValue = someType.fields.head
    // Pattern match unapply(scrut)
    // In case of None, return noneCase.
    // In case of Some(v), return someCase(v).
    def patternMatch(scrut: Expr, noneCase: Expr, someCase: Expr => Expr): Expr = {
      // We use this hand-coded if-then-else because we don't want to generate
      // match exhaustiveness checks in the program
      val binder = FreshIdentifier("unap", optionType, true)
      Let(
        binder,
        FunctionInvocation(unapplyFun, Seq(scrut)),
        IfExpr(
          IsInstanceOf(someType, Variable(binder)),
          someCase(CaseClassSelector(someType, Variable(binder), someValue.id)),
          noneCase
        )
      )
    }
    // Inlined .get method
    def get(scrut: Expr) = patternMatch(
      scrut,
      Error(optionType.tps.head, "None.get"),
      e => e
    )
    // Selects Some.v field without type-checking.
    // Use in a context where scrut.isDefined returns true.
    def getUnsafe(scrut: Expr) = CaseClassSelector(
      someType,
      FunctionInvocation(unapplyFun, Seq(scrut)),
      someValue.id
    )
  }

  /* Symbolic IO examples */
  case class Passes(in: Expr, out : Expr, cases : Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)

    val getType = leastUpperBound(cases.map(_.rhs.getType)) match {
      case None => untyped
      case Some(_) => BooleanType
    }

    def asConstraint = {
      val defaultCase = SimpleCase(WildcardPattern(None), out)
      Equals(out, MatchExpr(in, cases :+ defaultCase))
    }
  }


  /* Literals */
  sealed abstract class Literal[+T] extends Expr with Terminal {
    val value: T
  }

  case class CharLiteral(value: Char) extends Literal[Char] {
    val getType = CharType
  }

  case class IntLiteral(value: Int) extends Literal[Int] {
    val getType = Int32Type
  }
  case class InfiniteIntegerLiteral(value: BigInt) extends Literal[BigInt] {
    val getType = IntegerType
  }

  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    val getType = BooleanType
  }

  case class UnitLiteral() extends Literal[Unit] {
    val getType = UnitType
    val value = ()
  }


  /* Generic values. Represent values of the generic type tp */
  // TODO: Is it valid that GenericValue(tp, 0) != GenericValue(tp, 1)?
  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
    val getType = tp
  }


  /* Case classes */
  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr {
    val getType = checkParamTypes(args, ct.fieldsTypes, ct)
  }

  case class IsInstanceOf(classType: ClassType, expr: Expr) extends Expr {
    val getType = BooleanType
  }

  case class CaseClassSelector(classType: CaseClassType, caseClass: Expr, selector: Identifier) extends Expr {
    val selectorIndex = classType.classDef.selectorID2Index(selector)
    val getType = {
      // We don't demand equality because we may construct a mistyped field retrieval
      // (retrieving from a supertype before) passing it to the solver.
      // E.g. l.head where l:List[A] or even l: Nil[A]. This is ok for the solvers.
      if (typesCompatible(classType, caseClass.getType)) {
        classType.fieldsTypes(selectorIndex)
      } else {
        untyped
      }
    }
  }


  /* Equality */
  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (typesCompatible(lhs.getType, rhs.getType)) BooleanType
      else {
        untyped
      }
    }
  }


  /* Propositional logic */
  case class And(exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else untyped
    }
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  case class Or(exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else untyped
    }
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if(lhs.getType == BooleanType && rhs.getType == BooleanType) BooleanType
      else untyped
    }
  }

  case class Not(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == BooleanType) BooleanType
      else untyped
    }
  }


  /* Integer arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class UMinus(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  /*
   * Division and Remainder follows Java/Scala semantics. Division corresponds
   * to / operator on BigInt and Remainder corresponds to %. Note that in
   * Java/Scala % is called remainder and the "mod" operator (Modulo in Leon) is also
   * defined on BigInteger and differs from Remainder. The "mod" operator
   * returns an always positive remainder, while Remainder could return
   * a negative remainder. The following must hold:
   *
   *    Division(x, y) * y + Remainder(x, y) == x
   */
  case class Division(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class Remainder(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = BooleanType
  }
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = BooleanType
  }
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }


  /* Bit-vector arithmetic */
  case class BVPlus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVMinus(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVUMinus(expr: Expr) extends Expr { 
    require(expr.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVTimes(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVDivision(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVRemainder(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  case class BVNot(expr: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class BVAnd(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class BVOr(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class BVXOr(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }


  /* Tuple operations */

  // If you are not sure about the requirement you should use
  // the tupleWrap in purescala.Constructors
  case class Tuple (exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType)).unveilUntyped
  }

  /*
   * Index is 1-based, first element of tuple is 1.
   * If you are not sure that tuple is indeed of a TupleType,
   * you should use tupleSelect in pureScala.Constructors
   */
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    require(index >= 1)

    val getType = tuple.getType match {
      case TupleType(ts) =>
        require(index <= ts.size)
        ts(index - 1)

      case _ =>
        untyped
    }
  }


  /* Set operations */
  case class FiniteSet(elements: Set[Expr], base: TypeTree) extends Expr {
    val getType = SetType(base).unveilUntyped
  }
  case class ElementOfSet(element: Expr, set: Expr) extends Expr {
    val getType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr {
    val getType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr {
    val getType  = BooleanType
  }
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }

  // TODO: Add checks for these expressions too

  /* Map operations */
  case class FiniteMap(singletons: Seq[(Expr, Expr)], keyType: TypeTree, valueType: TypeTree) extends Expr {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  case class MapGet(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(from, to) if isSubtypeOf(key.getType, from) =>
        to
      case _ => untyped
    }
  }
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }
  case class MapDifference(map: Expr, keys: Expr) extends Expr {
    val getType = map.getType
  }
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr {
    val getType = BooleanType
  }


  /* Array operations */
  case class ArraySelect(array: Expr, index: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        untyped
    }
  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType).getOrElse(untyped).unveilUntyped
      case _ =>
        untyped
    }
  }

  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  case class NonemptyArray(elems: Map[Int, Expr], defaultLength: Option[(Expr, Expr)]) extends Expr {
    private val elements = elems.values.toList ++ defaultLength.map{_._1}
    val getType = ArrayType(optionToType(leastUpperBound(elements map { _.getType}))).unveilUntyped
  }

  case class EmptyArray(tpe: TypeTree) extends Expr with Terminal {
    val getType = ArrayType(tpe).unveilUntyped
  }


  /* Special trees for synthesis */

  case class Choose(pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(from, BooleanType) if from.nonEmpty => // @mk why nonEmpty?
        tupleTypeWrap(from)
      case _ =>
        untyped
    }
  }

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with Extractable {
    require(oracles.nonEmpty)

    val getType = body.getType

    def extract = {
      Some((Seq(body), (es: Seq[Expr]) => WithOracle(oracles, es.head).setPos(this)))
    }
  }

  case class Hole(tpe: TypeTree, alts: Seq[Expr]) extends Expr with Extractable {
    val getType = tpe

    def extract = {
      Some((alts, (es: Seq[Expr]) => Hole(tpe, es).setPos(this)))
    }
  }

}
