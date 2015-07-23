/* Copyright 2009-2015 EPFL, Lausanne */

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
  * If you are looking for things * such as function or class definitions, 
  * please have a look to [[purescala.Definitions]].
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
  * @define note_bitvector (32-bit vector)
  * @define note_real (Real)
  */
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


  /** Stands for an undefined Expr, similar to ??? or null */
  case class NoTree(tpe: TypeTree) extends Expr with Terminal {
    val getType = tpe
  }


  /* Specifications */

  /** This describes computational errors (unmatched case, taking min of an
    * empty set, division by zero, etc.). It should always be typed according to
    * the expected type. */
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
      else untyped
    }
  }

  /** Postcondition of an [[Expressions.Expr]]. Corresponds to the Leon keyword *ensuring*
    * 
    * @param body The body of the expression. It can contain at most one [[Expressions.Require]] sub-expression.
    * @param pred The predicate to satisfy. It should be a function whose argument's type can handle the type of the body */
  case class Ensuring(body: Expr, pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType) if isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        untyped
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
      else untyped
    }
  }


  /** Variable
    * @param id The identifier of this variable  */
  case class Variable(id: Identifier) extends Expr with Terminal {
    val getType = id.getType
  }


  /** $encodingof `val ... = ...; ...`
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#let purescala's constructor let]] or [[purescala.Constructors#letTuple purescala's constructor letTuple]]
    * 
    * @param binder The identifier used in body, defined just after '''val'''
    * @param value The value assigned to the identifier, after the '''=''' sign
    * @param body The expression following the ``val ... = ... ;` construct 
    */
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

  /** $encodingof `def ... = ...; ...` (local function definition)
    * 
    * @param id The function definition.
    * @param body The body of the expression after the function
    */
  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    val getType = body.getType
  }


  // OO Trees
  /** $encodingof `(...).method(args)` (method invocation)
    *
    * Both [[Expressions.MethodInvocation]] and [[Expressions.This]] get removed by phase [[MethodLifting]]. Methods become functions,
    * [[Expressions.This]] becomes first argument, and [[Expressions.MethodInvocation]] becomes [[Expressions.FunctionInvocation]].
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
      val extraMap: Map[TypeParameterDef, TypeTree] = rec.getType match {
        case ct: ClassType =>
          (cd.tparams zip ct.tps).toMap
        case _ =>
          Map()
      }
      instantiateType(fdret, extraMap)
    }
  }

  /** The '''this''' keyword */
  case class This(ct: ClassType) extends Expr with Terminal {
    val getType = ct
  }


  /* HOFs (Higher-order Functions) */
  
  /** $encodingof `callee(args...)`
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#application purescala's constructor application]]
    */
  case class Application(callee: Expr, args: Seq[Expr]) extends Expr {
    val getType = callee.getType match {
      case FunctionType(from, to) =>
        checkParamTypes(args, from, to)
      case _ =>
        untyped
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


  /* Control flow */
  /** $encodingof  `function(...)` (function invocation) */
  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    require(tfd.params.size == args.size)
    val getType = checkParamTypes(args, tfd.params, tfd.returnType)
  }

  /** $encodingof `if(...) ... else ...` */
  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(untyped).unveilUntyped
  }

  /** $encodingof `... match { ... }`
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#matchExpr purescala's constructor matchExpr]]
    * 
    * @param scrutinee Expression to the left of the '''match''' keyword
    * @param cases A sequence of cases to match `scrutinee` against 
    */
  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)
    val getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(untyped).unveilUntyped
  }

  /** $encodingof `case ... [if ...] => ... `
    * 
    * @param pattern The pattern just to the right of the '''case''' keyword
    * @param optGuard An optional if-condition just to the left of the `=>`
    * @param rhs The expression to the right of `=>`
    * @see [[Expressions.MatchExpr]]
    */
  case class MatchCase(pattern : Pattern, optGuard : Option[Expr], rhs: Expr) extends Tree {
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

  /** Pattern encoding `case a: ct` making sure an identifier is of the given type */
  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern { // c: Class
    val subPatterns = Seq()
  }
  /** Pattern encoding `case binder @ _ => ` with optional identifier `binder` */
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq()
  } 
  /** Pattern encoding `case CaseClass(...) =>` */
  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding tuple pattern `case (...) =>` */
  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding like `case 0 => ...` or `case "Foo" => ...` */
  case class LiteralPattern[+T](binder: Option[Identifier], lit : Literal[T]) extends Pattern {
    val subPatterns = Seq()    
  }

  /** A custom pattern defined through an object's `unapply` function */
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

  /** Symbolic I/O examples as a match/case.
    * $encodingof `out == in match { cases }`
    *  
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#passes purescala's constructor passes]]
    * 
    * @param in 
    * @param out
    */
  case class Passes(in: Expr, out : Expr, cases : Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)

    val getType = leastUpperBound(cases.map(_.rhs.getType)) match {
      case None => untyped
      case Some(_) => BooleanType
    }

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
  /** $encodingof a char literal */
  case class CharLiteral(value: Char) extends Literal[Char] {
    val getType = CharType
  }
  /** $encodingof an integer literal */
  case class IntLiteral(value: Int) extends Literal[Int] {
    val getType = Int32Type
  }
  /** $encodingof a big integer literal */
  case class InfiniteIntegerLiteral(value: BigInt) extends Literal[BigInt] {
    val getType = IntegerType
  }
  /** $encodingof a real literal */
  case class RealLiteral(value: BigDecimal) extends Literal[BigDecimal] {
    val getType = RealType
  }
  /** $encodingof a boolean literal '''true''' or '''false''' */
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    val getType = BooleanType
  }
  /** $encodingof a unit literal `()` */
  case class UnitLiteral() extends Literal[Unit] {
    val getType = UnitType
    val value = ()
  }


  /** Generic values. Represent values of the generic type `tp` */
  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
  // TODO: Is it valid that GenericValue(tp, 0) != GenericValue(tp, 1)?
    val getType = tp
  }


  /** $encodingof `CaseClass(args...)`
    * @param ct The case class name and inherited attributes
    * @param args The arguments of the case class
    */
  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr {
    val getType = checkParamTypes(args, ct.fieldsTypes, ct)
  }

  /** $encodingof `.isInstanceOf[...]` */
  case class IsInstanceOf(classType: ClassType, expr: Expr) extends Expr {
    val getType = BooleanType
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
        untyped
      }
    }
  }


  /** $encodingof `... == ...` */
  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (typesCompatible(lhs.getType, rhs.getType)) BooleanType
      else {
        untyped
      }
    }
  }


  /* Propositional logic */
  /** $encodingof `... && ...`
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#and purescala's constructor and]] or [[purescala.Constructors#andJoin purescala's constructor andJoin]]
    */
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

  /** $encodingof `... || ...`
    *  
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#or purescala's constructor or]] or [[purescala.Constructors#orJoin purescala's constructor orJoin]]
    */
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

  /** $encodingof `... ==> ...` (logical implication)
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#implies purescala's constructor implies]]
    */
  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if(lhs.getType == BooleanType && rhs.getType == BooleanType) BooleanType
      else untyped
    }
  }

  /** $encodingof `!...` */
  case class Not(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == BooleanType) BooleanType
      else untyped
    }
  }


  /* Integer arithmetic */

  /** $encodingof `... +  ...` for BigInts */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  /** $encodingof `... -  ...` */
  case class Minus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  /** $encodingof `- ... for BigInts`*/
  case class UMinus(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == IntegerType) IntegerType
      else untyped
    }
  }
  /** $encodingof `... * ...` */
  case class Times(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
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
      else untyped
    }
  }
  /** $encodingof `... %  ...` (can return negative numbers)
    *  
    * @see [[Expressions.Division]]
    */
  case class Remainder(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
    }
  }
  /** $encodingof `... mod  ...` (cannot return negative numbers)
    *  
    * @see [[Expressions.Division]]
    */
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (lhs.getType == IntegerType && rhs.getType == IntegerType) IntegerType
      else untyped
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
  /** $encodingof `... + ...` $note_bitvector*/
  case class BVPlus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `... - ...` $note_bitvector*/
  case class BVMinus(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `- ...` $note_bitvector*/
  case class BVUMinus(expr: Expr) extends Expr { 
    require(expr.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `... * ...` $note_bitvector*/
  case class BVTimes(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `... / ...` $note_bitvector*/
  case class BVDivision(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `... % ...` $note_bitvector*/
  case class BVRemainder(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }
  /** $encodingof `! ...` $note_bitvector*/
  case class BVNot(expr: Expr) extends Expr { 
    val getType = Int32Type
  }
  /** $encodingof `... & ...` $note_bitvector*/
  case class BVAnd(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `... | ...` $note_bitvector*/
  case class BVOr(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `... ^ ...` $note_bitvector*/
  case class BVXOr(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `... << ...` $note_bitvector*/
  case class BVShiftLeft(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `... >>> ...` $note_bitvector (logical shift)*/
  case class BVAShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `... >> ...` $note_bitvector (arighmetic shift, sign-preserving)*/
  case class BVLShiftRight(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }


  /* Real arithmetic */
  /** $encodingof `... + ...` $note_real */
  case class RealPlus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... - ...` $note_real */
  case class RealMinus(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `- ...` $note_real */
  case class RealUMinus(expr: Expr) extends Expr { 
    require(expr.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... * ...` $note_real */
  case class RealTimes(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }
  /** $encodingof `... / ...` $note_real */
  case class RealDivision(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == RealType && rhs.getType == RealType)
    val getType = RealType
  }


  /* Tuple operations */

  /** $encodingof `(..., ....)` (tuple)
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#tupleWrap purescala's constructor tupleWrap]]
    * 
    * @param exprs The expressions in the tuple
    */
  case class Tuple (exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType)).unveilUntyped
  }

  /** $encodingof `(tuple)._i`
    * 
    * Index is 1-based, first element of tuple is 1.
    * If you are not sure that tuple is indeed of a TupleType,
    * you should use [[purescala.Constructors$.tupleSelect(t:leon\.purescala\.Expressions\.Expr,index:Int,isTuple:Boolean):leon\.purescala\.Expressions\.Expr* purescala's constructor tupleSelect]]
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
  /** $encodingof `Set(elements)` */
  case class FiniteSet(elements: Set[Expr], base: TypeTree) extends Expr {
    val getType = SetType(base).unveilUntyped
  }
  /** $encodingof `set.contains(elements)` or `set(elements)` */
  case class ElementOfSet(element: Expr, set: Expr) extends Expr {
    val getType = BooleanType
  }
  /** $encodingof `set.length` */
  case class SetCardinality(set: Expr) extends Expr {
    val getType = Int32Type
  }
  /** $encodingof `set.subsetOf(set2)` */
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr {
    val getType  = BooleanType
  }
  /** $encodingof `set.intersect(set2)` */
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }
  /** $encodingof `set ++ set2` */
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }
  /** $encodingof `set -- set2` */
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(untyped).unveilUntyped
  }

  // TODO: Add checks for these expressions too

  /* Map operations */
  /** $encodingof `Map(key -> value, key2 -> value2 ...)` */
  case class FiniteMap(singletons: Seq[(Expr, Expr)], keyType: TypeTree, valueType: TypeTree) extends Expr {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  /** $encodingof `map.get(key)` */
  case class MapGet(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(from, to) if isSubtypeOf(key.getType, from) =>
        to
      case _ => untyped
    }
  }
  /** $encodingof `map ++ map2` */
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(untyped).unveilUntyped
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
        untyped
    }
  }

  /** $encodingof `array.updated(key, index)` */
  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType).getOrElse(untyped).unveilUntyped
      case _ =>
        untyped
    }
  }

  /** $encodingof `array.length` */
  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  /** $encodingof Array(...) with predetermined elements
    * @param elems The map from the position to the elements.  
    * @param defaultLength An optional pair where the first element is the default value and the second is the size of the array.
    */
  case class NonemptyArray(elems: Map[Int, Expr], defaultLength: Option[(Expr, Expr)]) extends Expr {
    private val elements = elems.values.toList ++ defaultLength.map{_._1}
    val getType = ArrayType(optionToType(leastUpperBound(elements map { _.getType}))).unveilUntyped
  }

  /** $encodingof `Array()` with a given type */
  case class EmptyArray(tpe: TypeTree) extends Expr with Terminal {
    val getType = ArrayType(tpe).unveilUntyped
  }


  /* Special trees for synthesis */
  /** $encodingof `choose(pred)` where pred should be a [[Types.FunctionType]] */
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

  /** $encodingof `???[tpe]` */
  case class Hole(tpe: TypeTree, alts: Seq[Expr]) extends Expr with Extractable {
    val getType = tpe

    def extract = {
      Some((alts, (es: Seq[Expr]) => Hole(tpe, es).setPos(this)))
    }
  }

}
