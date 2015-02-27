/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TreeOps.variablesOf
  import TypeTrees._
  import TypeTreeOps._
  import Definitions._
  import Extractors._
  import Constructors._


  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed with Serializable {
    // All Expr's have constant type
    override val getType: TypeTree
  }

  trait Terminal {
    self: Expr =>
  }

  case class NoTree(tpe: TypeTree) extends Expr with Terminal with Typed {
    val getType = tpe
  }

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(tpe: TypeTree, description: String) extends Expr with Terminal {
    val getType = tpe
  }

  case class Require(pred: Expr, body: Expr) extends Expr with Typed {
    val getType = body.getType
  }

  case class Ensuring(body: Expr, id: Identifier, pred: Expr) extends Expr {
    val getType = body.getType
  }

  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    val getType = body.getType
  }

  case class Choose(vars: List[Identifier], pred: Expr, var impl: Option[Expr] = None) extends Expr with NAryExtractable {
    require(!vars.isEmpty)

    val getType = tupleTypeWrap(vars.map(_.getType))

    def extract = {
      Some((Seq(pred)++impl, (es: Seq[Expr]) =>  Choose(vars, es.head, es.tail.headOption).setPos(this)))
    }
  }

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val getType = body.getType
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    val getType = body.getType
  }

  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    val getType = tfd.returnType
  }

  /**
   * OO Trees
   *
   * Both MethodInvocation and This get removed by phase MethodLifting. Methods become functions,
   * This becomes first argument, and MethodInvocation become FunctionInvocation.
   */
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    val getType = {
      // We need ot instanciate the type based on the type of the function as well as receiver
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

  case class Application(caller: Expr, args: Seq[Expr]) extends Expr {
    require(caller.getType.isInstanceOf[FunctionType])
    val getType = caller.getType.asInstanceOf[FunctionType].to
  }

  case class Lambda(args: Seq[ValDef], body: Expr) extends Expr {
    val getType = FunctionType(args.map(_.tpe), body.getType)
  }

  case class Forall(args: Seq[ValDef], body: Expr) extends Expr {
    require(body.getType == BooleanType)
    val getType = BooleanType
  }

  case class This(ct: ClassType) extends Expr with Terminal {
    val getType = ct
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped)
  }


  /*
   * If you are not sure about the requirement you should use 
   * the tupleWrap in purescala.Constructors
   */
  case class Tuple (exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType))
  }

  /*
   * Index is 1-based, first element of tuple is 1.
   * If you are not sure that tuple has a TupleType,
   * you should use tupleSelect in pureScala.Constructors
   */
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    require(index >= 1)

    val getType = tuple.getType match {
      case TupleType(ts) =>
        require(index <= ts.size)
        ts(index - 1)

      case _ =>
        Untyped
    }
  }

  abstract sealed class MatchLike extends Expr {
    val scrutinee : Expr
    val cases : Seq[MatchCase]  
    val getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(Untyped)
  }

  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends MatchLike {
    require(cases.nonEmpty)
  }
  
  case class Gives(scrutinee: Expr, cases : Seq[MatchCase]) extends MatchLike {
    def asMatchWithHole = {
      val theHole = SimpleCase(WildcardPattern(None), Hole(this.getType, Seq()))
      MatchExpr(scrutinee, cases :+ theHole)
    }

    def asMatch = {
      matchExpr(scrutinee, cases)
    }
  } 
  
  case class Passes(in: Expr, out : Expr, cases : Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)

    val getType = BooleanType
    
    def asConstraint = {
      val defaultCase = SimpleCase(WildcardPattern(None), out)
      Equals(out, MatchExpr(in, cases :+ defaultCase))
    }
  }


  case class MatchCase(pattern : Pattern, optGuard : Option[Expr], rhs: Expr) extends Tree {
    def expressions: Seq[Expr] = List(rhs) ++ optGuard
  }

  sealed abstract class Pattern extends Tree {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.map(_.binders).foldLeft[Set[Identifier]](Set.empty)(_ ++ _)
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


  /* Propositional logic */
  case class And(exprs: Seq[Expr]) extends Expr {
    val getType = BooleanType

    require(exprs.size >= 2)
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  case class Or(exprs: Seq[Expr]) extends Expr {
    val getType = BooleanType

    require(exprs.size >= 2)
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Not(expr: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }

  // tpe overrides the type of the identifier.
  // This is useful for variables that represent class fields with instantiated types.
  // E.g. list.head when list: List[Int]
  // @mk: TODO: This breaks symmetry with the rest of the trees and is ugly-ish.
  //      Feel free to rename the underlying class and define constructor/extractor,
  //      or do it some other way
  class Variable(val id: Identifier, val tpe: Option[TypeTree]) extends Expr with Terminal {
    val getType = tpe getOrElse id.getType
    override def equals(that: Any) = that match {
      case Variable(id2) => id == id2
      case _ => false
    }
    override def hashCode: Int = id.hashCode
  }

  object Variable {
    def apply(id: Identifier, tpe: Option[TypeTree] = None) = new Variable(id, tpe)
    def unapply(v: Variable) = Some(v.id)
  }

  /* Literals */
  sealed abstract class Literal[+T] extends Expr with Terminal {
    val value: T
  }

  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal {
    val getType = tp
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

  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr {
    val getType = ct
  }

  case class CaseClassInstanceOf(classType: CaseClassType, expr: Expr) extends Expr {
    val getType = BooleanType
  }

  object CaseClassSelector {
    def apply(classType: CaseClassType, caseClass: Expr, selector: Identifier): Expr = {
      caseClass match {
        case CaseClass(ct, fields) =>
          if (ct.classDef == classType.classDef) {
            fields(ct.classDef.selectorID2Index(selector))
          } else {
            new CaseClassSelector(classType, caseClass, selector)
          }
        case _ => new CaseClassSelector(classType, caseClass, selector)
      }
    }

    def unapply(ccs: CaseClassSelector): Option[(CaseClassType, Expr, Identifier)] = {
      Some((ccs.classType, ccs.caseClass, ccs.selector))
    }
  }

  class CaseClassSelector(val classType: CaseClassType, val caseClass: Expr, val selector: Identifier) extends Expr {
    val selectorIndex = classType.classDef.selectorID2Index(selector)
    val getType = classType.fieldsTypes(selectorIndex)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: CaseClassSelector => (t.classType, t.caseClass, t.selector) == (classType, caseClass, selector)
      case _ => false
    })

    override def hashCode: Int = (classType, caseClass, selector).hashCode + 9
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.getType == IntegerType && rhs.getType == IntegerType)
    val getType = IntegerType
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == IntegerType && rhs.getType == IntegerType)
    val getType = IntegerType
  }
  case class UMinus(expr: Expr) extends Expr { 
    require(expr.getType == IntegerType)
    val getType = IntegerType
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == IntegerType && rhs.getType == IntegerType)
    val getType = IntegerType
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == IntegerType && rhs.getType == IntegerType)
    val getType = IntegerType
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr { 
    require(lhs.getType == IntegerType && rhs.getType == IntegerType)
    val getType = IntegerType
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
  case class BVModulo(lhs: Expr, rhs: Expr) extends Expr { 
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

  /* Set expressions */
  case class NonemptySet(elements: Set[Expr]) extends Expr {
    require(elements.nonEmpty)
    val getType = SetType(leastUpperBound(elements.toSeq.map(_.getType))).unveilUntyped
  }
  
  case class EmptySet(tpe: TypeTree) extends Expr {
    val getType = SetType(tpe)
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
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }

  /* Map operations. */
  case class NonemptyMap(singletons: Seq[(Expr, Expr)]) extends Expr {
    require(singletons.nonEmpty)
    val getType = {
      val (keys, values) = singletons.unzip
      MapType(
        leastUpperBound(keys.map(_.getType)),
        leastUpperBound(values.map(_.getType))
      ).unveilUntyped
    }
  }
  
  case class EmptyMap(keyType: TypeTree, valueType: TypeTree) extends Expr {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  
  case class MapGet(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(from, to) => to
      case _ => Untyped
    }
  }
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(Untyped)
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
        Untyped
    }
  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    val getType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType(_)).getOrElse(Untyped)
      case _ =>
        Untyped
    }
  }

  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  case class NonemptyArray(elems: Map[Int, Expr], defaultLength: Option[(Expr, Expr)]) extends Expr {
    private val elements = elems.values.toList ++ defaultLength.map{_._1}
    val getType = ArrayType(leastUpperBound(elements map { _.getType})).unveilUntyped
  }

  case class EmptyArray(tpe: TypeTree) extends Expr {
    val getType = ArrayType(tpe).unveilUntyped
  }

  /* Special trees */

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with UnaryExtractable {
    require(!oracles.isEmpty)

    val getType = body.getType

    def extract = {
      Some((body, (e: Expr) => WithOracle(oracles, e).setPos(this)))
    }
  }

  case class Hole(tpe: TypeTree, alts: Seq[Expr]) extends Expr with NAryExtractable {
    val getType = tpe

    def extract = {
      Some((alts, (es: Seq[Expr]) => Hole(tpe, es).setPos(this)))
    }
  }

  /**
   * DEPRECATED TREES
   * These trees are not guaranteed to be supported by Leon.
   **/
  @deprecated("3.0", "Use NonemptyArray with default value")
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr {
    val getType = ArrayType(defaultValue.getType)
  }

  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class SetMin(set: Expr) extends Expr {
    val getType = Int32Type
  }

  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class SetMax(set: Expr) extends Expr {
    val getType = Int32Type
  }

  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class EmptyMultiset(baseType: TypeTree) extends Expr with Terminal {
    val getType = MultisetType(baseType).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class NonemptyMultiset(elements: Seq[Expr]) extends Expr {
    val getType = MultisetType(leastUpperBound(elements.toSeq.map(_.getType))).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetCardinality(multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr  {
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr { // disjoint union 
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr  {
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetToSet(multiset: Expr) extends Expr {
    val getType = multiset.getType match {
      case MultisetType(base) => SetType(base)
      case _ => Untyped
    }
  }


}
