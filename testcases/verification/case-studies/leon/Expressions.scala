/* Copyright 2009-2015 EPFL, Lausanne */

package leon.reflect.purescala

import leon._
import lang._
import string._
import collection._

import Common._
import Types._
import Definitions._
//import Extractors._
//import Constructors._
//import ExprOps.replaceFromIDs

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
  * @define note_bitvector (32-bit vector)
  * @define note_real (Real)
  */
object Expressions {

  private def checkParamTypes(real: List[Expr], formal: List[Expr], result: TypeTree): TypeTree = {
    if (real zip formal forall { case (real, formal) => true /* FIXME isSubtypeOf(real.getType, formal.getType)*/} ) {
      result.unveilUntyped
    } else {
      //println(real map { r => s"$r: ${r.getType}"} mkString ", " )
      //println(formal map { r => s"$r: ${r.getType}" } mkString ", " )
      Untyped
    }
  }

  abstract class Expr {
    val getType: TypeTree 
  }

  abstract class Terminal extends Expr

  /** Stands for an undefined Expr, similar to ??? or null */
  case class NoTree(tpe: TypeTree) extends Terminal {
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
  case class Error(tpe: TypeTree, description: String) extends Terminal {
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
    val getType = pred.getType match {
      case FunctionType(bodyType :: Nil(), BooleanType) => // FIXME if isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        Untyped
    }
    /** Converts this ensuring clause to the body followed by an assert statement */
    def toAssert: Expr = {
      val res = FreshIdentifier("res", getType, true)
      Let(res, body, Assert(
        Application(pred, List(Variable(res))), // FIXME application
        Some("Postcondition failed"), Variable(res)
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
  case class Variable(id: Identifier) extends Terminal {
    val getType = id.getType
  }


  /** $encodingof `val ... = ...; ...`
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#let purescala's constructor let]] or [[purescala.Constructors#letTuple purescala's constructor letTuple]]
    * 
    * @param binder The identifier used in body, defined just after '''val'''
    * @param value The value assigned to the identifier, after the '''=''' sign
    * @param body The expression following the ``val ... = ... ;`` construct
    */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val getType = {
      // We can't demand anything sticter here, because some binders are
      // typed context-wise
      if (true) // FIXME (typesCompatible(value.getType, binder.getType))
        body.getType
      else {
        Untyped
      }
    }
  }

  /** $encodingof `def ... = ...; ...` (local function definition)
    * 
    * @param fd The function definition.
    * @param body The body of the expression after the function
    */
  case class LetDef(fd: FunDef, body: Expr) extends Expr {
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
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: List[Expr]) extends Expr {
    val getType = {
      // We need ot instantiate the type based on the type of the function as well as receiver
      val fdret = tfd.returnType
      val extraMap: Map[TypeParameterDef, TypeTree] = rec.getType match {
        case ct: ClassType =>
          ListOps.toMap(cd.tparams zip ct.tps)
        case _ =>
          Map[TypeParameterDef, TypeTree]()
      }
      fdret // FIXME instantiateType(fdret, extraMap)
    }
  }

  /** $encodingof the '''this''' keyword
    * Both [[Expressions.MethodInvocation]] and [[Expressions.This]] get removed by phase [[MethodLifting]].
    * Methods become functions, [[Expressions.This]] becomes first argument,
    * and [[Expressions.MethodInvocation]] becomes [[Expressions.FunctionInvocation]].
    */
  case class This(ct: TypeTree) extends Terminal {
    def isLegal = ct.isInstanceOf[ClassType]
    val getType = ct
  }


  /* Higher-order Functions */
  
  /** $encodingof `callee(args...)` */
  case class Application(callee: Expr, args: List[Expr]) extends Expr {
    val getType = callee.getType match {
      case FunctionType(from, to) =>
        to // FIXME checkParamTypes(args, from, to)
      case _ =>
        Untyped
    }
  }

  /** $encodingof `(args) => body` */
  case class Lambda(args: List[ValDef], body: Expr) extends Expr {
    val getType = FunctionType(args.map(_.getType), body.getType).unveilUntyped
    def paramSubst(realArgs: List[Expr]) = {
      require(realArgs.size == args.size)
      ListOps.toMap(args map { _.id } zip realArgs)
    }
    def withParamSubst(realArgs: List[Expr], e: Expr) = e /*{
      replaceFromIDs(paramSubst(realArgs), e)
    }*/
  }


  /* Control flow */

  /** $encodingof  `function(...)` (function invocation) */
  case class FunctionInvocation(tfd: TypedFunDef, args: List[Expr]) extends Expr {
    require(tfd.params.size == args.size)
    val getType = tfd.returnType // FIXME checkParamTypes(args, tfd.params, tfd.returnType)
  }

  /** $encodingof `if(...) ... else ...` */
  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = Untyped // FIXME leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `... match { ... }`
    * 
    * If `cases` might be empty you should use
    * [[purescala.Constructors#matchExpr purescala's constructor matchExpr]]
    * 
    * @param scrutinee Expression to the left of the '''match''' keyword
    * @param cases A Listuence of cases to match `scrutinee` against 
    */
  case class MatchExpr(scrutinee: Expr, cases: List[MatchCase]) extends Expr {
    require(cases.nonEmpty)
    val getType = Untyped // FIXME leastUpperBound(cases.map(_.rhs.getType)).getOrElse(Untyped).unveilUntyped
  }

  /** $encodingof `case ... [if ...] => ... `
    * 
    * @param pattern The pattern just to the right of the '''case''' keyword
    * @param optGuard An optional if-condition just to the left of the `=>`
    * @param rhs The expression to the right of `=>`
    * @see [[Expressions.MatchExpr]]
    */
  case class MatchCase(pattern : Pattern, optGuard : Option[Expr], rhs: Expr) {
    def expressions: List[Expr] = optGuard.toList :+ rhs
  }

  /** $encodingof a pattern after a '''case''' keyword.
    * 
    * @see [[Expressions.MatchCase]]
    */
  sealed abstract class Pattern {
    val subPatterns: List[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.flatMap(pat => setToList(pat.binders)).toSet
    def binders: Set[Identifier] = subBinders ++ binder.toSet

  }

  /** Pattern encoding `case a: ct` making sure an identifier is of the given type */
  case class InstanceOfPattern(binder: Option[Identifier], ct: TypeTree) extends Pattern { // c: Class
    def isLegal = ct.isInstanceOf[ClassType]
    val subPatterns = List[Pattern]()
  }
  /** Pattern encoding `case binder @ _ => ` with optional identifier `binder` */
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = List[Pattern]()
  } 
  /** Pattern encoding `case CaseClass(...) =>` */
  case class CaseClassPattern(binder: Option[Identifier], ct: TypeTree, subPatterns: List[Pattern]) extends Pattern {
    def isLegal = ct.isInstanceOf[CaseClassType]
  }

  /** Pattern encoding tuple pattern `case (...) =>` */
  case class TuplePattern(binder: Option[Identifier], subPatterns: List[Pattern]) extends Pattern

  /** Pattern encoding like `case 0 => ...` or `case "Foo" => ...` */
  case class LiteralPattern(binder: Option[Identifier], lit : Expr) extends Pattern {
    def isLegal = lit.isInstanceOf[Literal]
    val subPatterns = List[Pattern]()    
  }


  /** Literals */
  sealed abstract class Literal extends Terminal {
    //val value: T
  }
  /** $encodingof a char literal */
  case class CharLiteral(value: Char) extends Literal {
    val getType = CharType
  }
  /** $encodingof a 32-bit integer literal */
  case class IntLiteral(value: Int) extends Literal {
    val getType = Int32Type
  }
  /** $encodingof an infinite precision integer literal */
  case class InfiniteIntegerLiteral(value: BigInt) extends Literal {
    val getType = IntegerType
  }

  /** $encodingof a boolean literal '''true''' or '''false''' */
  case class BooleanLiteral(value: Boolean) extends Literal {
    val getType = BooleanType
  }
  /** $encodingof a unit literal `()` */
  case class UnitLiteral() extends Literal {
    val getType = UnitType
    val value = ()
  }


  /** $encodingof `CaseClass(args...)`
    * @param ct The case class name and inherited attributes
    * @param args The arguments of the case class
    */
  case class CaseClass(ct: TypeTree, args: List[Expr]) extends Expr {
    def isLegal = ct.isInstanceOf[CaseClassType]
    val getType = Untyped // FIXME checkParamTypes(args, ct.fieldsTypes, ct)
  }

  /** $encodingof `.isInstanceOf[...]` */
  case class IsInstanceOf(classType: TypeTree, expr: Expr) extends Expr {
    def isLegal = classType.isInstanceOf[ClassType]
    val getType = BooleanType
  }

  /**
   * $encodingof `.asInstanceOf[...]` 
   * Introduced by matchToIfThenElse to transform match-cases to type-correct
   * if bodies.
   */
  case class AsInstanceOf(expr: Expr, tpe: TypeTree) extends Expr {
    def isLegal = tpe.isInstanceOf[ClassType]
    val getType = tpe
  }

  /** $encodingof `value.selector` where value is of a case class type
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#caseClassSelector purescala's constructor caseClassSelector]]
    */
  case class CaseClassSelector(classType: TypeTree, caseClass: Expr, selector: Identifier) extends Expr { // FIXME ClassType
    def isLegal = classType.isInstanceOf[CaseClassType]
    
    val selectorIndex = {
      require(isLegal)
      classType.asInstanceOf[CaseClassType].classDef.asInstanceOf[CaseClassDef].selectorID2Index(selector)
    }
    
    val getType = {
      require(isLegal)
      // We don't demand equality because we may construct a mistyped field retrieval
      // (retrieving from a supertype before) passing it to the solver.
      // E.g. l.head where l:List[A] or even l: Nil[A]. This is ok for the solvers.
      if (true) { // FIXME (typesCompatible(classType, caseClass.getType)) {
        classType.asInstanceOf[CaseClassType].fieldsTypes(selectorIndex)
      } else {
        Untyped
      }
    }
  }


  /** $encodingof `... == ...` */
  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if (true) BooleanType // FIXME (typesCompatible(lhs.getType, rhs.getType)) BooleanType
      else {
        Untyped
      }
    }
  }


  /* Propositional logic */
  /** $encodingof `... && ...`
    *
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#and purescala's constructor and]] or [[purescala.Constructors#andJoin purescala's constructor andJoin]]
    */
  case class And(exprs: List[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else Untyped
    }
  }

  /** $encodingof `... || ...`
    *  
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#or purescala's constructor or]] or [[purescala.Constructors#orJoin purescala's constructor orJoin]]
    */
  case class Or(exprs: List[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = {
      if (exprs forall (_.getType == BooleanType)) BooleanType
      else Untyped
    }
  }

  /** $encodingof `... ==> ...` (logical implication)
    * 
    * If you are not sure about the requirement you should use
    * [[purescala.Constructors#implies purescala's constructor implies]]
    */
  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    val getType = {
      if(lhs.getType == BooleanType && rhs.getType == BooleanType) BooleanType
      else Untyped
    }
  }

  /** $encodingof `!...` */
  case class Not(expr: Expr) extends Expr {
    val getType = {
      if (expr.getType == BooleanType) BooleanType
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
  case class LesListuals(lhs: Expr, rhs: Expr) extends Expr { 
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
    * Tuples should always contain at least 2 elements.
    * If you are not sure about this requirement, you should use
    * [[purescala.Constructors#tupleWrap purescala's constructor tupleWrap]]
    * 
    * @param exprs The expressions in the tuple
    */
  case class Tuple (exprs: List[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType)).unveilUntyped
  }

  /** $encodingof `(tuple)._i`
    * 
    * Index is 1-based, first element of tuple is 1.
    * If you are not sure that tuple is indeed of a TupleType,
    * you should use [[purescala.Constructors$.tupleSelect(t:leon\.purescala\.Expressions\.Expr,index:Int,isTuple:Boolean):leon\.purescala\.Expressions\.Expr* purescala's constructor tupleSelect]]
    */
  case class TupleSelect(tuple: Expr, index: BigInt) extends Expr {

    def isLegal = index >= 1

    val getType = {
      require(isLegal)
      tuple.getType match {
        case TupleType(ts) if index <= ts.size =>
          ts(index - 1)
        case _ =>
          Untyped
      }
    }
  }


  /* Set operations */
  /** $encodingof `Set(elements)` */
  case class FiniteSet(elements: List[Expr], base: TypeTree) extends Expr {
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
    val getType = Untyped // FIXME leastUpperBound(List(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  /** $encodingof `set ++ set2` */
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = Untyped // FIXME leastUpperBound(List(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  /** $encodingof `set -- set2` */
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = Untyped // FIXME leastUpperBound(List(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  // TODO: Add checks for these expressions too

  /* Map operations */
  /** $encodingof `Map(key -> value, key2 -> value2 ...)` */
  case class FiniteMap(singletons: List[(Expr, Expr)], keyType: TypeTree, valueType: TypeTree) extends Expr {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  /** $encodingof `map.get(key)` */
  case class MapGet(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(from, to) => // FIXME if isSubtypeOf(key.getType, from) =>
        to
      case _ => Untyped
    }
  }
  /** $encodingof `map ++ map2` */
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = Untyped // FIXME leastUpperBound(List(map1, map2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  /** $encodingof `map -- map2` */
  case class MapDifference(map: Expr, keys: Expr) extends Expr {
    val getType = map.getType
  }
  /** $encodingof `map.isDefinedAt(key)` */
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr {
    val getType = BooleanType
  }



  /* Special trees for synthesis */
  /** $encodingof `choose(pred)` where pred should be a [[Types.FunctionType]] */
  case class Choose(pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(from, BooleanType) if from.nonEmpty => // @mk why nonEmpty?
        TupleType(from) // FIXME tupleTypeWrap(from)
      case _ =>
        Untyped
    }
  }

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr { // FIXME with Extractable {
    require(oracles.nonEmpty)

    val getType = body.getType

    // FIXME: This reveals a bug in Z3
    //def extract = {
    //  Some((List(body), (es: List[Expr]) => WithOracle(oracles, es.head)))
    //}
  }

  /** $encodingof `???[tpe]` */
  case class Hole(tpe: TypeTree, alts: List[Expr]) extends Expr { // FIXME with Extractable {
    val getType = tpe

    //def extract = {
    //  Some((alts, (es: List[Expr]) => Hole(tpe, es)))
    //}
  }

}
