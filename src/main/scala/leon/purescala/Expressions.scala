/* Copyright 2009-2016 EPFL, Lausanne */

package leon.purescala

import Common._
import Types._
import TypeOps._
import Definitions._
import Extractors._
import Constructors._
import ExprOps.replaceFromIDs

/** Expression definitions for Pure Scala.
  *
  * If you are looking for things such as function or class definitions,
  * please have a look in [[purescala.Definitions]].
  *
  * Every expression in Leon inherits from [[Expr]]. The AST definitions are simple
  * case classes, with no behaviour. In particular, they do not perform smart
  * rewriting. What you build is what you get. For example,
  * {{{
  * And(BooleanLiteral(true), Variable(id)) != Variable(id)
  * }}}
  * because the ``And`` constructor will simply build a tree without checking for
  * optimization opportunities. Unless you need exact control on the structure
  * of the trees, you should use constructors in [[purescala.Constructors]], that
  * simplify the trees they produce.
  *
  * @define encodingof Encoding of
  * @define noteBitvector (32-bit vector)
  * @define noteReal (Real)
  */
object Expressions {

  private def checkParamTypes(real: Seq[Typed], formal: Seq[Typed], result: TypeTree): TypeTree = {
    if (real zip formal forall { case (real, formal) => isSubtypeOf(real.getType, formal.getType)} ) {
      result.unveilUntyped
    } else {
      //println(s"Failed to type as $result")
      //println(real map { r => s"$r: ${r.getType}"} mkString ", " )
      //println(formal map { r => s"$r: ${r.getType}" } mkString ", " )
      Untyped
    }
  }

  /** Represents an expression in Leon. */
  abstract class Expr extends Tree with Typed

  /** Trait which gets mixed-in to expressions without subexpressions */
  trait Terminal {
    self: Expr =>
  }


  /** Stands for an undefined Expr, similar to `???` or `null`
    *
    * During code generation, it gets compiled to `null`, or the 0 of the
    * respective type for value types.
    */
  case class NoTree(tpe: TypeTree) extends Expr with Terminal {
    val getType = tpe
  }


  /* Specifications */

  /** Computational errors (unmatched case, taking min of an empty set,
    * division by zero, etc.). Corresponds to the ``error[T](description)``
    * Leon library function.
    * It should always be typed according to the expected type.
    *
    * @param tpe The type of this expression
    * @param description The description of the error
    */
  case class Error(tpe: TypeTree, description: String) extends Expr with Terminal {
    val getType = tpe
  }

  /** Precondition of an [[Expressions.Expr]]. Corresponds to the Leon keyword *require*
    *
    * @param pred The precondition formula inside ``require(...)``
    * @param body The body following the ``require(...)``
    */
  case class Require(pred: Expr, body: Expr) extends Expr {
    val getType = {
      if (pred.getType == BooleanType)
        body.getType
      else Untyped
    }
  }

  /** Postcondition of an [[Expressions.Expr]]. Corresponds to the Leon keyword *ensuring*
    *
    * @param body The body of the expression. It can contain at most one [[Expressions.Require]] sub-expression.
    * @param pred The predicate to satisfy. It should be a function whose argument's type can handle the type of the body
    */
  case class Ensuring(body: Expr, pred: Expr) extends Expr {
    require(pred.isInstanceOf[Lambda])

    val getType = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType) if isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        Untyped
    }
    /** Converts this ensuring clause to the body followed by an assert statement */
    def toAssert: Expr = {
      val res = FreshIdentifier("res", getType, true)
      Let(res, body, Assert(
        application(pred, Seq(Variable(res))),
        Some("Postcondition failed @" + this.getPos), Variable(res)
      ))
    }
  }

  /** Local assertions with customizable error message
    *
    * @param pred The predicate, first argument of `assert(..., ...)`
    * @param error An optional error string to display if the assert fails. Second argument of `assert(..., ...)`
    * @param body The expression following `assert(..., ...)`
    */
  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    val getType = {
      if (pred.getType == BooleanType)
        body.getType
      else Untyped
    }
  }


  /** Variable
    * @param id The identifier of this variable
    */
  case class Variable(id: Identifier) extends Expr with Terminal {
    val getType = id.getType
  }


  /** $encodingof `val ... = ...; ...`
    *
    * @param binder The identifier used in body, defined just after '''val'''
    * @param value The value assigned to the identifier, after the '''=''' sign
    * @param body The expression following the ``val ... = ... ;`` construct
    * @see [[purescala.Constructors#let purescala's constructor let]]
    */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val getType = {
      // We can't demand anything stricter here, because some binders are
      // typed context-wise
      if (typesCompatible(value.getType, binder.getType))
        body.getType
      else {
        Untyped
      }
    }
  }

  /** $encodingof multiple `def ... = ...; ...` (local function definition and possibly mutually recursive)
    *
    * @param fds The function definitions.
    * @param body The body of the expression after the function
    */
  case class LetDef(fds: Seq[FunDef], body: Expr) extends Expr {
    require(fds.nonEmpty)
    val getType = body.getType
  }


  /* OO Trees */

  /** $encodingof `(...).method(args)` (method invocation)
    *
    * Both [[Expressions.MethodInvocation]] and [[Expressions.This]] get removed by phase [[MethodLifting]].
    * Methods become functions, [[Expressions.This]] becomes first argument,
    * and [[Expressions.MethodInvocation]] becomes [[Expressions.FunctionInvocation]].
    *
    * @param rec The expression evaluating to an object
    * @param cd The class definition typing `rec`
    * @param tfd The typed function definition of the method
    * @param args The arguments provided to the method
    */
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    val getType = {
      // We need ot instantiate the type based on the type of the function as well as receiver
      val fdret = tfd.returnType
      val extraMap: Map[TypeParameter, TypeTree] = rec.getType match {
        case ct: ClassType =>
          (cd.typeArgs zip ct.tps).toMap
        case _ =>
          Map()
      }
      instantiateType(fdret, extraMap)
    }
  }

  case class ArrayForall(array: Expr, from: Expr, to: Expr, body: Expr) extends Expr {
    require(body.getType match {
      case FunctionType(_, BooleanType) => true
      case _ => false
    })
    val getType = BooleanType
  }
  case class ArrayExists(array: Expr, from: Expr, to: Expr, body: Expr) extends Expr {
    require(body.getType match {
      case FunctionType(_, BooleanType) => true
      case _ => false
    })
    val getType = BooleanType
  }

  case class BoundedForall(from: Expr, to: Expr, body: Expr) extends Expr {
    val intType = from.getType
    require((intType == IntegerType || intType == Int32Type) && from.getType == to.getType)
    require(body.getType match {
      case FunctionType(Seq(IntegerType), BooleanType) => intType == IntegerType
      case FunctionType(Seq(Int32Type), BooleanType) => intType == Int32Type
      case _ => false
    })
    val getType = BooleanType
  }
  case class BoundedExists(from: Expr, to: Expr, body: Expr) extends Expr {
    val intType = from.getType
    require((intType == IntegerType || intType == Int32Type) && from.getType == to.getType)
    require(body.getType match {
      case FunctionType(Seq(IntegerType), BooleanType) => intType == IntegerType
      case FunctionType(Seq(Int32Type), BooleanType) => intType == Int32Type
      case _ => false
    })
    val getType = BooleanType
  }

  /** $encodingof the '''this''' keyword
    * Both [[Expressions.MethodInvocation]] and [[Expressions.This]] get removed by phase [[MethodLifting]].
    * Methods become functions, [[Expressions.This]] becomes first argument,
    * and [[Expressions.MethodInvocation]] becomes [[Expressions.FunctionInvocation]].
    */
  case class This(ct: ClassType) extends Expr with Terminal {
    val getType = ct
  }


  /* Higher-order Functions */

  /** $encodingof `callee(args...)`, where [[callee]] is an expression of a function type (not a method) */
  case class Application(callee: Expr, args: Seq[Expr]) extends Expr {
    val getType = callee.getType match {
      case FunctionType(from, to) =>
        checkParamTypes(args, from, to)
      case _ =>
        Untyped
    }
  }

  /** $encodingof `(args) => body` */
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

  case class FiniteLambda(mapping: Seq[(Seq[Expr], Expr)], default: Expr, tpe: FunctionType) extends Expr {
    val getType = tpe
  }

  /* Universal Quantification */

  case class Forall(args: Seq[ValDef], body: Expr) extends Expr {
    val getType = BooleanType
  }

  /* Control flow */

  /** $encodingof  `function(...)` (function invocation) */
  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    require(tfd.params.size == args.size)
    val getType = checkParamTypes(args, tfd.params, tfd.returnType)
  }

  /** $encodingof `if(...) ... else ...` */
  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = leastUpperBound(thenn.getType, elze.getType)
  }

  /** $encodingof `... match { ... }`
    *
    * '''cases''' should be nonempty. If you are not sure about this, you should use
    * [[purescala.Constructors#matchExpr purescala's constructor matchExpr]]
    *
    * @param scrutinee Expression to the left of the '''match''' keyword
    * @param cases A sequence of cases to match `scrutinee` against
    */
  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)
    val getType = leastUpperBound(cases.map(_.rhs.getType))
  }

  /** $encodingof `case pattern [if optGuard] => rhs`
    *
    * @param pattern The pattern just to the right of the '''case''' keyword
    * @param optGuard An optional if-condition just to the left of the `=>`
    * @param rhs The expression to the right of `=>`
    * @see [[Expressions.MatchExpr]]
    */
  case class MatchCase(pattern: Pattern, optGuard: Option[Expr], rhs: Expr) extends Tree {
    def expressions: Seq[Expr] = optGuard.toList :+ rhs
  }

  /** $encodingof a pattern after a '''case''' keyword.
    *
    * @see [[Expressions.MatchCase]]
    */
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

  /** Pattern encoding `case binder: ct`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern {
    val subPatterns = Seq()
  }
  /** Pattern encoding `case _ => `, or `case binder => ` if identifier [[binder]] is present */
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq()
  }
  /** Pattern encoding `case binder @ ct(subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding tuple pattern `case binder @ (subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding like `case binder @ 0 => ...` or `case binder @ "Foo" => ...`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class LiteralPattern[+T](binder: Option[Identifier], lit : Literal[T]) extends Pattern {
    val subPatterns = Seq()
  }

  /** A custom pattern defined through an object's `unapply` function */
  case class UnapplyPattern(binder: Option[Identifier], unapplyFun: TypedFunDef, subPatterns: Seq[Pattern]) extends Pattern {
    // Hacky, but ok
    lazy val optionType = unapplyFun.returnType.asInstanceOf[AbstractClassType]
    lazy val Seq(noneType, someType) = optionType.knownCCDescendants.sortBy(_.fields.size)
    lazy val someValue = someType.classDef.fields.head

    /** Construct a pattern matching against unapply(scrut) (as an if-expression)
      *
      * @param scrut The scrutinee of the pattern matching
      * @param noneCase The expression that will happen if unapply(scrut) is None
      * @param someCase How unapply(scrut).get will be handled in case it exists
      */
    def patternMatch(scrut: Expr, noneCase: Expr, someCase: Expr => Expr): Expr = {
      // We use this hand-coded if-then-else because we don't want to generate
      // match exhaustiveness checks in the program
      val binder = FreshIdentifier("unap", optionType, true)
      Let(
        binder,
        FunctionInvocation(unapplyFun, Seq(scrut)),
        IfExpr(
          IsInstanceOf(Variable(binder), someType),
          someCase(CaseClassSelector(someType, Variable(binder), someValue.id)),
          noneCase
        )
      )
    }

    /** Inlined .get method */
    def get(scrut: Expr) = patternMatch(
      scrut,
      Error(optionType.tps.head, "None.get"),
      e => e
    )

    /** Selects Some.v field without type-checking.
      * Use in a context where scrut.isDefined returns true.
      */
    def getUnsafe(scrut: Expr) = CaseClassSelector(
      someType,
      FunctionInvocation(unapplyFun, Seq(scrut)),
      someValue.id
    )

    def isSome(scrut: Expr) = IsInstanceOf(FunctionInvocation(unapplyFun, Seq(scrut)), someType)

  }

  // Extracts without taking care of the binder. (contrary to Extractos.Pattern)
  object PatternExtractor extends TreeExtractor[Pattern] {
    def unapply(e: Pattern): Option[(Seq[Pattern], (Seq[Pattern]) => Pattern)] = e match {
      case (_: InstanceOfPattern) | (_: WildcardPattern) | (_: LiteralPattern[_]) =>
        Some(Seq(), es => e)
      case CaseClassPattern(binder, ct, subpatterns) =>
        Some(subpatterns, es => CaseClassPattern(binder, ct, es))
      case TuplePattern(binder, subpatterns) =>
        Some(subpatterns, es => TuplePattern(binder, es))
      case UnapplyPattern(binder, unapplyFun, subpatterns) =>
        Some(subpatterns, es => UnapplyPattern(binder, unapplyFun, es))
      case _ => None
    }
  }

  object PatternOps extends GenTreeOps[Pattern] {
    val Deconstructor = PatternExtractor
  }

  /** Symbolic I/O examples as a match/case.
    * $encodingof `out == (in match { cases; case _ => out })`
    *
    * [[cases]] should be nonempty. If you are not sure about this, you should use
    * [[purescala.Constructors#passes purescala's constructor passes]]
    *
    * @param in The input expression
    * @param out The output expression
    * @param cases The cases to compare against
    */
  case class Passes(in: Expr, out: Expr, cases: Seq[MatchCase]) extends Expr {
    //require(cases.nonEmpty)

    val getType =
      if (leastUpperBound(cases.map(_.rhs.getType)) == Untyped) Untyped
      else BooleanType

    /** Transforms the set of I/O examples to a constraint equality. */
    def asConstraint = {
      val defaultCase = SimpleCase(WildcardPattern(None), out)
      Equals(out, MatchExpr(in, cases :+ defaultCase))
    }
  }


  /** Literals */
  sealed abstract class Literal[+T] extends Expr with Terminal {
    val value: T
  }
  /** $encodingof a character literal */
  case class CharLiteral(value: Char) extends Literal[Char] {
    val getType = CharType
  }
  /** $encodingof a 8-bit integer literal */
  case class ByteLiteral(value: Byte) extends Literal[Byte] {
    val getType = Int8Type
  }
  /** $encodingof a 32-bit integer literal */
  case class IntLiteral(value: Int) extends Literal[Int] {
    val getType = Int32Type
  }
  /** $encodingof an infinite precision integer literal */
  case class InfiniteIntegerLiteral(value: BigInt) extends Literal[BigInt] {
    val getType = IntegerType
  }
  /** $encodingof a fraction literal */
  case class FractionalLiteral(numerator: BigInt, denominator: BigInt) extends Literal[(BigInt, BigInt)] {
    val value = (numerator, denominator)
    val getType = RealType
  }
  /** $encodingof a boolean literal '''true''' or '''false''' */
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    val getType = BooleanType
  }
  /** $encodingof the unit literal `()` */
  case class UnitLiteral() extends Literal[Unit] {
    val getType = UnitType
    val value = ()
  }
  /** $encodingof a string literal */
  case class StringLiteral(value: String) extends Literal[String] {
    val getType = StringType
  }


  /** Generic values. Represent values of the generic type `tp`.
    * This is useful e.g. to present counterexamples of generic types.
    */
  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
    val getType = tp
  }


  /** $encodingof `ct(args...)`
    *
    * @param ct The case class name and inherited attributes
    * @param args The arguments of the case class
    */
  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr {
    val getType = checkParamTypes(args, ct.fieldsTypes, ct)
  }

  /** $encodingof `.isInstanceOf[...]` */
  case class IsInstanceOf(expr: Expr, classType: ClassType) extends Expr {
    val getType = BooleanType
  }

  /** $encodingof `expr.asInstanceOf[tpe]`
    *
    * Introduced by matchToIfThenElse to transform match-cases to type-correct
    * if bodies.
    */
  case class AsInstanceOf(expr: Expr, tpe: ClassType) extends Expr {
    val getType = tpe
  }

  /** $encodingof `value.selector` where value is of a case class type
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#caseClassSelector purescala's constructor caseClassSelector]]
    */
  case class CaseClassSelector(classType: CaseClassType, caseClass: Expr, selector: Identifier) extends Expr {
    val selectorIndex = classType.classDef.selectorID2Index(selector)
    val getType = {
      // We don't demand equality because we may construct a mistyped field retrieval
      // (retrieving from a supertype before) passing it to the solver.
      // E.g. l.head where l:List[A] or even l: Nil[A]. This is ok for the solvers.
      if (typesCompatible(classType, caseClass.getType)) {
        classType.fieldsTypes(selectorIndex)
      } else {
        Untyped
      }
    }
  }


  /** $encodingof `... == ...` */
  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (typesCompatible(lhs.getType, rhs.getType)) BooleanType
      else {
        //println(s"Incompatible argument types: arguments: ($lhs, $rhs) types: ${lhs.getType}, ${rhs.getType}")
        Untyped
      }
    }
  }


  /* Propositional logic */
  /** $encodingof `... && ...`
    *
    * [[exprs]] must contain at least two elements; if you are not sure about this,
    * you should use [[purescala.Constructors#and purescala's constructor and]]
    * or [[purescala.Constructors#andJoin purescala's constructor andJoin]]
    */
  case class And(exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else Untyped
    }
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  /** $encodingof `... || ...`
    *
    * [[exprs]] must contain at least two elements; if you are not sure about this,
    * you should use [[purescala.Constructors#or purescala's constructor or]] or
    * [[purescala.Constructors#orJoin purescala's constructor orJoin]]
    */
  case class Or(exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else Untyped
    }
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  /** $encodingof `... ==> ...` (logical implication).
    *
    * This is not a standard Scala operator, but it results from an implicit
    * conversion in the Leon library.
    *
    * @see [[leon.purescala.Constructors.implies]]
    */
  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if(lhs.getType == BooleanType && rhs.getType == BooleanType) BooleanType
      else Untyped
    }
  }

  /** $encodingof `!...`
    *
    * @see [[leon.purescala.Constructors.not]]
    */
  case class Not(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == BooleanType) BooleanType
      else Untyped
    }
  }

  abstract class ConverterToString(fromType: TypeTree, toType: TypeTree) extends Expr {
    def expr: Expr
    val getType = if(expr.getType == fromType) toType else Untyped
  }

  /* String Theory */
  /** $encodingof `expr.toString` for Int32 to String */
  case class Int32ToString(expr: Expr) extends ConverterToString(Int32Type, StringType)
  /** $encodingof `expr.toString` for boolean to String */
  case class BooleanToString(expr: Expr) extends ConverterToString(BooleanType, StringType)
  /** $encodingof `expr.toString` for BigInt to String */
  case class IntegerToString(expr: Expr) extends ConverterToString(IntegerType, StringType)
  /** $encodingof `expr.toString` for char to String */
  case class CharToString(expr: Expr) extends ConverterToString(CharType, StringType)
  /** $encodingof `expr.toString` for real to String */
  case class RealToString(expr: Expr) extends ConverterToString(RealType, StringType)
  /** $encodingof `lhs + rhs` for strings */
  case class StringConcat(lhs: Expr, rhs: Expr) extends Expr {
     val getType = {
      if (lhs.getType == StringType && rhs.getType == StringType) StringType
      else Untyped
    }
  }
  /** $encodingof `lhs.subString(start, end)` for strings */
  case class SubString(expr: Expr, start: Expr, end: Expr) extends Expr {
    val getType = {
      val ext = expr.getType
      val st = start.getType
      val et = end.getType
      if (ext == StringType && st == Int32Type && et == Int32Type) StringType
      else Untyped
    }
  }
  /** $encodingof `lhs.subString(start, end)` for strings */
  case class BigSubString(expr: Expr, start: Expr, end: Expr) extends Expr {
    val getType = {
      val ext = expr.getType
      val st = start.getType
      val et = end.getType
      if (ext == StringType && st == IntegerType && et == IntegerType) StringType
      else Untyped
    }
  }
  /** $encodingof `lhs.length` for strings */
  case class StringLength(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == StringType) Int32Type
      else Untyped
    }
  }
  /** $encodingof `lhs.length` for strings */
  case class StringBigLength(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == StringType) IntegerType
      else Untyped
    }
  }

  /* Integer arithmetic */

  /** $encodingof `... +  ...` for BigInts */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `... -  ...` */
  case class Minus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `- ... for BigInts`*/
  case class UMinus(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `... * ...` */
  case class Times(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `... /  ...`
    *
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
      else Untyped
    }
  }
  /** $encodingof `... %  ...` (can return negative numbers)
    *
    * @see [[Expressions.Division]]
    */
  case class Remainder(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `... mod  ...` (cannot return negative numbers)
    *
    * @see [[Expressions.Division]]
    */
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else Untyped
    }
  }
  /** $encodingof `... < ...`*/
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }
  /** $encodingof `... > ...`*/
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }
  /** $encodingof `... <= ...`*/
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }
  /** $encodingof `... >= ...`*/
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }


  /* Bit-vector arithmetic */
  /** $encodingof `... + ...` $noteBitvector*/
  case class BVPlus(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... - ...` $noteBitvector*/
  case class BVMinus(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `- ...` $noteBitvector*/
  case class BVUMinus(expr: Expr) extends Expr {
    require(isBVType(expr.getType))
    val getType = expr.getType
  }
  /** $encodingof `... * ...` $noteBitvector*/
  case class BVTimes(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... / ...` $noteBitvector*/
  case class BVDivision(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... % ...` $noteBitvector*/
  case class BVRemainder(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `! ...` $noteBitvector */
  case class BVNot(expr: Expr) extends Expr {
    require(isBVType(expr.getType))
    val getType = expr.getType
  }
  /** $encodingof `... & ...` $noteBitvector */
  case class BVAnd(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... | ...` $noteBitvector */
  case class BVOr(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... ^ ...` $noteBitvector */
  case class BVXOr(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... << ...` $noteBitvector */
  case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... >> ...` $noteBitvector (arithmetic shift, sign-preserving) */
  case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }
  /** $encodingof `... >>> ...` $noteBitvector (logical shift) */
  case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    require(areSameBVType(lhs.getType, rhs.getType))
    val getType = lhs.getType
  }

  /** TODO Doc (format???) */
  case class BVNarrowingCast(expr: Expr, newType: BitVectorType) extends Expr {
    require(expr.getType match {
      case BVType(size) if size > newType.size => true
      case _ => false
    })
    val getType = newType
    val from = expr.getType.asInstanceOf[BitVectorType].size
    val to = newType.size
  }
  /** TODO Doc (format???) */
  case class BVWideningCast(expr: Expr, newType: BitVectorType) extends Expr {
    require(expr.getType match {
      case BVType(size) if size < newType.size => true
      case _ => false
    })
    val getType = newType
    val from = expr.getType.asInstanceOf[BitVectorType].size
    val to = newType.size
  }


  /* Real arithmetic */
  /** $encodingof `... + ...` $noteReal */
  case class RealPlus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... - ...` $noteReal */
  case class RealMinus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `- ...` $noteReal */
  case class RealUMinus(expr: Expr) extends Expr {
    require(expr.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... * ...` $noteReal */
  case class RealTimes(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... / ...` $noteReal */
  case class RealDivision(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }


  /* Tuple operations */

  /** $encodingof `(..., ....)` (tuple)
    *
    * [[exprs]] should always contain at least 2 elements.
    * If you are not sure about this requirement, you should use
    * [[leon.purescala.Constructors.tupleWrap purescala's constructor tupleWrap]]
    *
    * @param exprs The expressions in the tuple
    */
  case class Tuple(exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType)).unveilUntyped
  }

  /** $encodingof `(tuple)._i`
    *
    * Index is 1-based, first element of tuple is 1.
    * If you are not sure that [[tuple]] is indeed of a TupleType,
    * you should use [[leon.purescala.Constructors.tupleSelect(t:leon\.purescala\.Expressions\.Expr,index:Int,isTuple:Boolean):leon\.purescala\.Expressions\.Expr* purescala's constructor tupleSelect]]
    */
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    require(index >= 1)

    val getType = tuple.getType match {
      case tp@TupleType(ts) =>
        require(index <= ts.size, s"Got index $index for '$tuple' of type '$tp")
        ts(index - 1)

      case _ =>
        Untyped
    }
  }


  /* Set operations */

  /** $encodingof `Set[base](elements)` */
  case class FiniteSet(elements: Set[Expr], base: TypeTree) extends Expr {
    val getType = SetType(base).unveilUntyped
  }
  /** $encodingof `set + elem` */
  case class SetAdd(set: Expr, elem: Expr) extends Expr {
    val getType = {
      val base = set.getType match {
        case SetType(base) => base
        case _ => Untyped
      }
      checkParamTypes(Seq(elem.getType), Seq(base), SetType(base).unveilUntyped)
    }
  }
  /** $encodingof `set.contains(element)` or `set(element)` */
  case class ElementOfSet(element: Expr, set: Expr) extends Expr {
    val getType = checkParamTypes(Seq(element.getType), Seq(set.getType match {
      case SetType(base) => base
      case _ => Untyped
    }), BooleanType)
  }
  /** $encodingof `set.length` */
  case class SetCardinality(set: Expr) extends Expr {
    val getType = IntegerType
  }
  /** $encodingof `set.subsetOf(set2)` */
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr {
    val getType = (set1.getType, set2.getType) match {
      case (SetType(b1), SetType(b2)) if b1 == b2 => BooleanType
      case _ => Untyped
    }
  }
  /** $encodingof `set & set2` */
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType))
  }
  /** $encodingof `set ++ set2` */
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType))
  }
  /** $encodingof `set -- set2` */
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType))
  }

  /* Bag operations */
  /** $encodingof `Bag[base](elements)` */
  case class FiniteBag(elements: Map[Expr, Expr], base: TypeTree) extends Expr {
    val getType = BagType(base).unveilUntyped
  }
  /** $encodingof `bag + elem` */
  case class BagAdd(bag: Expr, elem: Expr) extends Expr {
    val getType = {
      val base = bag.getType match {
        case BagType(base) => base
        case _ => Untyped
      }
      checkParamTypes(Seq(base), Seq(elem.getType), BagType(base).unveilUntyped)
    }
  }
  /** $encodingof `bag.get(element)` or `bag(element)` */
  case class MultiplicityInBag(element: Expr, bag: Expr) extends Expr {
    val getType = checkParamTypes(Seq(element.getType), Seq(bag.getType match {
      case BagType(base) => base
      case _ => Untyped
    }), IntegerType)
  }
  /** $encodingof `bag1 & bag2` */
  case class BagIntersection(bag1: Expr, bag2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(bag1, bag2).map(_.getType))
  }
  /** $encodingof `bag1 ++ bag2` */
  case class BagUnion(bag1: Expr, bag2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(bag1, bag2).map(_.getType))
  }
  /** $encodingof `bag1 -- bag2` */
  case class BagDifference(bag1: Expr, bag2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(bag1, bag2).map(_.getType))
  }


  // TODO: Add checks for these expressions too

  /* Map operations */
  /** $encodingof `Map[keyType, valueType](key1 -> value1, key2 -> value2 ...)` */
  case class FiniteMap(pairs: Map[Expr, Expr], keyType: TypeTree, valueType: TypeTree) extends Expr {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  /** $encodingof `map.apply(key)` (or `map(key)`)*/
  case class MapApply(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(from, to) if isSubtypeOf(key.getType, from) =>
        to
      case _ => Untyped
    }
  }
  /** $encodingof `map ++ map2` */
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(map1, map2).map(_.getType))
  }
  /** $encodingof `map -- map2` */
  case class MapDifference(map: Expr, keys: Expr) extends Expr {
    val getType = map.getType
  }
  /** $encodingof `map.isDefinedAt(key)` */
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr {
    val getType = BooleanType
  }


  /* Array operations */
  /** $encodingof `array(key)` */
  case class ArraySelect(array: Expr, index: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        Untyped
    }
  }

  /** $encodingof `array.updated(key, index)` */
  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        ArrayType(leastUpperBound(base, newValue.getType)).unveilUntyped
      case _ =>
        Untyped
    }
  }

  /** $encodingof `array.length` */
  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  /** $encodingof Array(elems...) with predetermined elements
    * @param elems The map from the position to the elements.
    * @param defaultLength An optional pair where the first element is the default value
    *                      and the second is the size of the array. Set this for big arrays
    *                      with a default value (as genereted with `Array.fill` in Scala).
    */
  case class NonemptyArray(elems: Map[Int, Expr], defaultLength: Option[(Expr, Expr)]) extends Expr {
    require(elems.nonEmpty || (defaultLength.nonEmpty && defaultLength.get._2 != IntLiteral(0)))
    private val elements = elems.values.toList ++ defaultLength.map(_._1)
    val getType = ArrayType(leastUpperBound(elements map { _.getType })).unveilUntyped
  }

  /** $encodingof `Array[tpe]()` */
  case class EmptyArray(tpe: TypeTree) extends Expr with Terminal {
    val getType = ArrayType(tpe).unveilUntyped
  }

  /* Special trees for synthesis */
  /** $encodingof `choose(pred)`, the non-deterministic choice in Leon.
    *
    * The semantics of this expression is some value
    * @note [[pred]] should be a of a [[Types.FunctionType]].
    */
  case class Choose(pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(from, BooleanType) if from.nonEmpty => // @mk why nonEmpty?
        tupleTypeWrap(from)
      case _ =>
        Untyped
    }
  }

  /** Provide an oracle (synthesizable, all-seeing choose) */
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with Extractable {
    require(oracles.nonEmpty)

    val getType = body.getType

    def extract = {
      Some((Seq(body), (es: Seq[Expr]) => WithOracle(oracles, es.head).setPos(this)))
    }
  }

  /** $encodingof a synthesizable hole in a program. Represented by `???[tpe]`
    * in Leon source code.
    *
    * A [[Hole]] gets transformed into a [[Choose]] construct during [[leon.synthesis.ConversionPhase the ConvertHoles phase]].
    */
  case class Hole(tpe: TypeTree, alts: Seq[Expr]) extends Expr with Extractable {
    val getType = tpe

    def extract = {
      Some((alts, (es: Seq[Expr]) => Hole(tpe, es).setPos(this)))
    }
  }

}
