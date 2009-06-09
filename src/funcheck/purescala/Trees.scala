package funcheck.purescala

import Common._

/** AST definitions for Pure Scala. */
object Trees {

  /* EXPRESSIONS */

  /** There's no such thing as a typing phase for these trees, they need to be
   * correctly typed at construction time. Each AST node checks that the
   * children provided satisfy whatever typing constraints are required by the
   * node, and each node is then responsible for communicating its type. */
  sealed abstract class Expr extends Typed {
    override def toString: String = PrettyPrinter(this)
  }

  /** 
   Go through each type, add the operations.
     map update
     concatenation of lists
     random access on lists
     set union, intersection, etc.

   Lambda abstraction and application of function values

   Separately, function calls

   equality on sets, ADTs etc. (equality on function types?!)

   forall, exists - optionally bounded quantifiers
     * comes with type A of bound variable 
     * also comes with an optional Set[A] that gives more precise description of the range of this variable

    Without Set[A] bound, the variable ranges over all constructible (not only allocated) objects.

see examples in:
     http://code.google.com/p/scalacheck/wiki/UserGuide
   */

  /* Control flow */
  case class FunctionInvocation(funDef: FunDef, args: Seq[Expr]) extends Expr {
    assert(args.map(_.getType).equalsWith(funDef.argTypes)(_ == _))
    lazy val getType = funDef.returnType
  }

  case class IfExpr(cond : Expr, then : Expr, elze : Expr) extends Expr {
    assert(cond.getType == BooleanType)
    assert(then.getType == elze.getType)
    def getType = then.getType
  }

  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    // there can be no assumption about the type of the scrutinee..  Scala
    // gives nice errors "constructor cannot be instantiated to expected type"
    // but that seems relatively hard to check at construction for now...
    // Actually it only gives that error when the pattern is unapply (ie. not
    // an "instanceOf" one), so there's hope.
    
    // we should assert that the rhs types of all MatchCases match !

    lazy val getType = cases(0).rhs.getType
  }

  sealed abstract class MatchCase {
    val pattern: Pattern
    val rhs: Expr
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase
  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    assert(guard.getType == BooleanType)
  }

  sealed abstract class Pattern
  case class InstanceOfPattern(binder: Option[Identifier], classTypeDef: ClassTypeDef) extends Pattern // c: Class
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern // c @ _
  case class ExtractorPattern(binder: Option[Identifier], 
			      extractor : ExtractorTypeDef, 
			      subPatterns: Seq[Pattern]) extends Pattern // c @ Extractor(...,...)
  // I suggest we skip Seq stars for now.

  /* Propositional logic */
  case class And(exprs: Seq[Expr]) extends Expr {
    assert(exprs.forall(_.getType == BooleanType))
    def getType = BooleanType
  }

  case class Or(exprs: Seq[Expr]) extends Expr {
    assert(exprs.forall(_.getType == BooleanType))
    def getType = BooleanType
  }

  case class Not(expr: Expr) extends Expr {
    assert(expr.getType == BooleanType)
    def getType = BooleanType
  }

  /* Not sure if we should really have these.. I suppose they could be of some
   * help to some theorem provers? *
  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == BooleanType && rhs.getType == BooleanType)
    def getType = BooleanType
  }

  case class Iff(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == BooleanType && rhs.getType == BooleanType)
    def getType = BooleanType
  } */

  /* Maybe we should split this one depending on types? */
  case class Equals(left: Expr, right: Expr) extends Expr { 
    assert(left.getType == right.getType)
    val getType = BooleanType
  }
  
  /* Literals */
  // to be fixed! Should contain a reference to the definition of that
  // variable, which would also give us its type.
  case class Variable(id: Identifier) extends Expr {
    val getType = AnyType
  }

  case class IntLiteral(value: Int) extends Expr {
    val getType = Int32Type
  }

  case class BooleanLiteral(value: Boolean) extends Expr {
    val getType = BooleanType
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }

  case class Minus(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }

  case class UMinus(expr: Expr) extends Expr {
    assert(expr.getType == Int32Type)
    val getType = Int32Type
  }

  case class Times(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }

  case class Division(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = Int32Type
  }

  case class LessThan(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = BooleanType
  }

  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = BooleanType
  }

  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = BooleanType
  }

  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr {
    assert(lhs.getType == Int32Type && rhs.getType == Int32Type)
    val getType = BooleanType
  }

  /* Option expressions */
  case class OptionSome(value: Expr) extends Expr {
    lazy val getType = OptionType(value.getType)
  }

  case class OptionNone(baseType: TypeTree) extends Expr {
    lazy val getType = OptionType(baseType)
  }

  /* Set expressions */
  case class EmptySet(baseType: TypeTree) extends Expr {
    lazy val getType = SetType(baseType)
  }
  case class FiniteSet(elements: Seq[Expr]) extends Expr {
    assert(elements.size > 0)
    assert(elements.drop(1).forall(_.getType == elements(0).getType))
    lazy val getType = SetType(elements(0).getType)
  }
  case class ElementOfSet(element: Expr, set: Expr) extends Expr {
    assert(set.getType == SetType(element.getType))
    val getType = BooleanType
  }
  case class IsEmptySet(set: Expr) extends Expr {
    assert(set.getType.isInstanceOf[SetType])
    val getType = BooleanType
  }
  case class SetEquals(set1: Expr, set2: Expr) extends Expr {
    assert(set1.getType == set2.getType && set1.getType.isInstanceOf[SetType])
    val getType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr {
    assert(set.getType.isInstanceOf[SetType])
    val getType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr {
    assert(set1.getType == set2.getType && set1.getType.isInstanceOf[SetType])
    val getType = BooleanType
  }
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    assert(set1.getType == set2.getType && set1.getType.isInstanceOf[SetType])
    lazy val getType = set1.getType
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    assert(set1.getType == set2.getType && set1.getType.isInstanceOf[SetType])
    lazy val getType = set1.getType
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    assert(set1.getType == set2.getType && set1.getType.isInstanceOf[SetType])
    lazy val getType = set1.getType
  }

  /* Multiset expressions */
  case class EmptyMultiset(baseType: TypeTree) extends Expr {
    lazy val getType = MultisetType(baseType)
  }
  case class FiniteMultiset(elements: Seq[Expr]) extends Expr {
    assert(elements.size > 0)
    assert(elements.drop(1).forall(_.getType == elements(0).getType))
    lazy val getType = MultisetType(elements(0).getType)
  }
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr {
    assert(multiset.getType == MultisetType(element.getType))
    val getType = Int32Type
  }
  case class IsEmptyMultiset(multiset: Expr) extends Expr {
    assert(multiset.getType.isInstanceOf[MultisetType])
    val getType = BooleanType
  }
  case class MultisetEquals(multiset1: Expr, multiset2: Expr) extends Expr {
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    val getType = BooleanType
  }
  case class MultisetCardinality(multiset: Expr) extends Expr {
    assert(multiset.getType.isInstanceOf[MultisetType])
    val getType = Int32Type
  }
  case class SubmultisetOf(multiset1: Expr, multiset2: Expr) extends Expr {
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    val getType = BooleanType
  }
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr {
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    lazy val getType = multiset1.getType
  }
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr {
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    lazy val getType = multiset1.getType
  }
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr { // disjoint union
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    lazy val getType = multiset1.getType
  }
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr {
    assert(multiset1.getType == multiset2.getType && multiset1.getType.isInstanceOf[MultisetType])
    lazy val getType = multiset1.getType
  }

  /* Map operations. */
  case class EmptyMap(fromType: TypeTree, toType: TypeTree) extends Expr {
    lazy val getType = MapType(fromType, toType)
  }

  case class SingletonMap(from: Expr, to: Expr) extends Expr {
    lazy val getType = MapType(from.getType, to.getType)
  }

  case class FiniteMap(singletons: Seq[SingletonMap]) extends Expr {
    assert(singletons.size > 0
      && singletons.drop(1).forall(_.getType == singletons(0).getType))
    lazy val getType = singletons(0).getType
  }

  case class MapGet(map: Expr, key: Expr) extends Expr {
    assert(map.getType.isInstanceOf[MapType] && key.getType == map.getType.asInstanceOf[MapType].from)
    lazy val getType = OptionType(map.getType.asInstanceOf[MapType].to)
  }

  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    assert(map1.getType.isInstanceOf[MapType] && map1.getType == map2.getType)
    lazy val getType = map1.getType
  }

  case class MapDiffrence(map: Expr, keys: Expr) extends Expr {
    assert(map.getType.isInstanceOf[MapType] && keys.isInstanceOf[SetType] && map.getType.asInstanceOf[MapType].from == keys.getType.asInstanceOf[SetType].base)
    lazy val getType = map.getType
  }

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr {
    lazy val getType = ListType(baseType)
  }

  case class Cons(head: Expr, tail: Expr) extends Expr {
    assert(tail.isInstanceOf[ListType] && tail.getType.asInstanceOf[ListType].base == head.getType)
    lazy val getType = tail.getType
  }

  case class Car(list: Expr) extends Expr {
    assert(list.getType.isInstanceOf[ListType])
    lazy val getType = list.getType.asInstanceOf[ListType].base
  }

  case class Cdr(list: Expr) extends Expr {
    assert(list.getType.isInstanceOf[ListType])
    lazy val getType = list.getType
  }

  case class Concat(list1: Expr, list2: Expr) extends Expr {
    assert(list1.getType.isInstanceOf[ListType] && list1.getType == list2.getType)
    lazy val getType = list1.getType
  }

  case class ListAt(list: Expr, index: Expr) extends Expr {
    assert(list.getType.isInstanceOf[ListType] && index.getType == Int32Type)
    lazy val getType = OptionType(list.getType.asInstanceOf[ListType].base)
  }

  /* TYPES */

  trait Typed {
    def getType: TypeTree
  }

  sealed abstract class TypeTree

  case object AnyType extends TypeTree
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class FunctionType(arg: TypeTree, res: TypeTree) extends TypeTree
  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class ClassType(id: Identifier) extends TypeTree
  case class CaseClassType(id: Identifier) extends TypeTree
  case class OptionType(base: TypeTree) extends TypeTree

  /* DEFINTIONS */

  type VarDecl = (Identifier,TypeTree)
  type VarDecls = Seq[VarDecl]

  sealed abstract class Definition(name : Identifier)

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassTypeDef
  sealed trait ExtractorTypeDef

  case class CaseClassDef(name : Identifier, fields : VarDecls) extends Definition(name) with ClassTypeDef with ExtractorTypeDef
  case class ClassDef(name : Identifier, fields : VarDecls) extends Definition(name) with ClassTypeDef
  // case class ExtractorDef extends FunDef ...
  
  case class ValDef(name : Identifier, value : Expr) extends Definition(name)
  case class FunDef(name : Identifier, args : VarDecls, body : Expr) extends Definition(name) {
    lazy val argTypes : Seq[TypeTree] = args.map(_._2) 
    lazy val returnType : TypeTree = body.getType
  }
  case class ObjectDef(name : Identifier, defs : Seq[Definition]) extends Definition(name)
}
