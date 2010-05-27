package purescala

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import Definitions._

  /* EXPRESSIONS */

  sealed abstract class Expr extends Typed {
    override def toString: String = PrettyPrinter(this)
  }

  /* Control flow */
  case class FunctionInvocation(funDef: FunDef, args: Seq[Expr]) extends Expr
  case class IfExpr(cond: Expr, then: Expr, elze: Expr) extends Expr 
  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr

  sealed abstract class MatchCase {
    val pattern: Pattern
    val rhs: Expr
    val theGuard: Option[Expr]
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase {
    val theGuard = None
  }
  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    val theGuard = Some(guard)
  }

  sealed abstract class Pattern
  case class InstanceOfPattern(binder: Option[Identifier], classTypeDef: ClassTypeDef) extends Pattern // c: Class
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern // c @ _
  case class CaseClassPattern(binder: Option[Identifier], caseClassDef: CaseClassDef, subPatterns: Seq[Pattern]) extends Pattern
  // case class ExtractorPattern(binder: Option[Identifier], 
  //   		      extractor : ExtractorTypeDef, 
  //   		      subPatterns: Seq[Pattern]) extends Pattern // c @ Extractor(...,...)
  // We don't handle Seq stars for now.

  /* Propositional logic */
  case object And {
    def apply(l: Expr, r: Expr): Expr = (l,r) match {
      case (And(exs1), And(exs2)) => And(exs1 ++ exs2)
      case (And(exs1), ex2) => And(exs1 :+ ex2)
      case (ex1, And(exs2)) => And(exs2 :+ ex1)
      case (ex1, ex2) => And(List(ex1, ex2))
    }
  }

  case object Or {
    def apply(l: Expr, r: Expr): Expr = (l,r) match {
      case (Or(exs1), Or(exs2)) => Or(exs1 ++ exs2)
      case (Or(exs1), ex2) => Or(exs1 :+ ex2)
      case (ex1, Or(exs2)) => Or(exs2 :+ ex1)
      case (ex1, ex2) => Or(List(ex1, ex2))
    }
  }

  case class And(exprs: Seq[Expr]) extends Expr
  case class Or(exprs: Seq[Expr]) extends Expr
  case class Not(expr: Expr) extends Expr 

  /* Maybe we should split this one depending on types? */
  case class Equals(left: Expr, right: Expr) extends Expr  
  
  /* Literals */
  case class Variable(id: Identifier) extends Expr {
    override def getType = id.getType
    override def setType(tt: TypeTree) = { id.setType(tt); this }
  }

  // represents the result in post-conditions
  case class ResultVariable() extends Expr

  sealed abstract class Literal[T] extends Expr {
    val value: T
  }

  case class IntLiteral(value: Int) extends Literal[Int] 
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] 
  case class StringLiteral(value: String) extends Literal[String]

  case class CaseClass(classDef: CaseClassDef, args: Seq[Expr]) extends Expr
  case class CaseClassSelector(caseClass: Expr, selector: Identifier) extends Expr

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr
  case class Minus(lhs: Expr, rhs: Expr) extends Expr 
  case class UMinus(expr: Expr) extends Expr 
  case class Times(lhs: Expr, rhs: Expr) extends Expr 
  case class Division(lhs: Expr, rhs: Expr) extends Expr 
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr 
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr 
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr 
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr 

  /* Option expressions */
  case class OptionSome(value: Expr) extends Expr 
  case class OptionNone(baseType: TypeTree) extends Expr 

  /* Set expressions */
  case class EmptySet(baseType: TypeTree) extends Expr 
  case class FiniteSet(elements: Seq[Expr]) extends Expr 
  case class ElementOfSet(element: Expr, set: Expr) extends Expr 
  case class IsEmptySet(set: Expr) extends Expr 
  case class SetEquals(set1: Expr, set2: Expr) extends Expr 
  case class SetCardinality(set: Expr) extends Expr 
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr 
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr 
  case class SetUnion(set1: Expr, set2: Expr) extends Expr 
  case class SetDifference(set1: Expr, set2: Expr) extends Expr 

  /* Multiset expressions */
  // case class EmptyMultiset(baseType: TypeTree) extends Expr 
  // case class FiniteMultiset(elements: Seq[Expr]) extends Expr 
  // case class Multiplicity(element: Expr, multiset: Expr) extends Expr 
  // case class IsEmptyMultiset(multiset: Expr) extends Expr 
  // case class MultisetEquals(multiset1: Expr, multiset2: Expr) extends Expr 
  // case class MultisetCardinality(multiset: Expr) extends Expr 
  // case class SubmultisetOf(multiset1: Expr, multiset2: Expr) extends Expr 
  // case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr 
  // case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr 
  // case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr // disjoint union
  // case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr 

  /* Map operations. */
  case class EmptyMap(fromType: TypeTree, toType: TypeTree) extends Expr 
  case class SingletonMap(from: Expr, to: Expr) extends Expr 
  case class FiniteMap(singletons: Seq[SingletonMap]) extends Expr 

  case class MapGet(map: Expr, key: Expr) extends Expr 
  case class MapUnion(map1: Expr, map2: Expr) extends Expr 
  case class MapDiffrence(map: Expr, keys: Expr) extends Expr 

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr 
  case class Cons(head: Expr, tail: Expr) extends Expr 
  case class Car(list: Expr) extends Expr 
  case class Cdr(list: Expr) extends Expr 
  case class Concat(list1: Expr, list2: Expr) extends Expr 
  case class ListAt(list: Expr, index: Expr) extends Expr 
}
