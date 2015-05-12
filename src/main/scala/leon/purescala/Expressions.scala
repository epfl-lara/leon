/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Types._
import TypeOps._
import Definitions._
import Extractors._
import Constructors._

/** AST definitions for Pure Scala. */
object Expressions {

  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed

  trait Terminal {
    self: Expr =>
  }

  case class NoTree(tpe: TypeTree) extends Expr with Terminal {
    val getType = tpe
  }

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(tpe: TypeTree, description: String) extends Expr with Terminal {
    val getType = tpe
  }

  case class Require(pred: Expr, body: Expr) extends Expr {
    val getType = body.getType
  }

  case class Ensuring(body: Expr, pred: Expr) extends Expr {
    val getType = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType) if bodyType == body.getType => bodyType
      case _ => Untyped
    }
    def toAssert: Expr = {
      val res = FreshIdentifier("res", getType, true)
      Let(res, body, Assert(application(pred, Seq(Variable(res))), Some("Postcondition failed @" + this.getPos), Variable(res)))
    }
  }

  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    val getType = body.getType
  }

  case class Choose(pred: Expr, private var impl_ : Option[Expr] = None) extends Expr {
    val getType = pred.getType match {
      case FunctionType(from, to) if from.nonEmpty => // @mk why nonEmpty? 
        tupleTypeWrap(from)
      case _ =>
        Untyped
    }

    require(impl_ forall { imp => isSubtypeOf(imp.getType, this.getType)})

    def impl_= (newImpl: Option[Expr]) = { 
      require(
        newImpl forall {imp => isSubtypeOf(imp.getType,this.getType)}, 
        newImpl.get +":" + newImpl.get.getType + " vs " + this + ":" + this.getType
      )
      impl_ = newImpl
    }

    def impl = impl_
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
    val getType = FunctionType(args.map(_.getType), body.getType).unveilUntyped
  }

  case class Forall(args: Seq[ValDef], body: Expr) extends Expr {
    require(body.getType == BooleanType)
    val getType = BooleanType
  }

  case class This(ct: ClassType) extends Expr with Terminal {
    val getType = ct
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped).unveilUntyped
  }


  /*
   * If you are not sure about the requirement you should use 
   * the tupleWrap in purescala.Constructors
   */
  case class Tuple (exprs: Seq[Expr]) extends Expr {
    require(exprs.size >= 2)
    val getType = TupleType(exprs.map(_.getType)).unveilUntyped
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

  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    require(cases.nonEmpty)
    val getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(Untyped).unveilUntyped
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

  case class Variable(id: Identifier) extends Expr with Terminal {
    val getType = id.getType
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
  /*
   * Division and Modulo follows Java/Scala semantics. Division corresponds
   * to / operator on BigInt and Modulo corresponds to %. Note that in
   * Java/Scala % is rather called remainder and the "mod" operator is also
   * defined on BigInteger and differs from our Modulo. The "mod" operator
   * returns an always positive remainder, while our Modulo could return
   * a negative remainder. The following must hold:
   *
   *    Division(x, y) * y + Modulo(x, y) == x
   */
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
    val getType = SetType(optionToType(leastUpperBound(elements.toSeq.map(_.getType)))).unveilUntyped
  }
  
  case class EmptySet(tpe: TypeTree) extends Expr with Terminal {
    val getType = SetType(tpe).unveilUntyped
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
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }

  /* Map operations. */
  case class NonemptyMap(singletons: Seq[(Expr, Expr)]) extends Expr {
    require(singletons.nonEmpty)
    val getType = {
      val (keys, values) = singletons.unzip
      MapType(
        optionToType(leastUpperBound(keys.map(_.getType))),
        optionToType(leastUpperBound(values.map(_.getType)))
      ).unveilUntyped
    }
  }
  
  case class EmptyMap(keyType: TypeTree, valueType: TypeTree) extends Expr with Terminal {
    val getType = MapType(keyType, valueType).unveilUntyped
  }
  
  case class MapGet(map: Expr, key: Expr) extends Expr {
    val getType = map.getType match {
      case MapType(_, to) => to
      case _ => Untyped
    }
  }
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    val getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(Untyped).unveilUntyped
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
        leastUpperBound(base, newValue.getType).map(ArrayType).getOrElse(Untyped).unveilUntyped
      case _ =>
        Untyped
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

  /* Special trees */

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with UnaryExtractable {
    require(oracles.nonEmpty)

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
    val getType = ArrayType(defaultValue.getType).unveilUntyped
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
    val getType = MultisetType(optionToType(leastUpperBound(elements.toSeq.map(_.getType)))).unveilUntyped
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
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr  {
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr { // disjoint union 
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr  {
    val getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped).unveilUntyped
  }
  @deprecated("3.0", "Leon does not guarantee to correctly handle this expression")
  case class MultisetToSet(multiset: Expr) extends Expr {
    val getType = multiset.getType match {
      case MultisetType(base) => SetType(base).unveilUntyped
      case _ => Untyped
    }
  }


}
