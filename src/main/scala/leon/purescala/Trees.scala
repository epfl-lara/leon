/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import utils._

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import TypeTreeOps._
  import Definitions._
  import Extractors._
  import Constructors._


  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed with Serializable

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
    def getType = body.getType
  }

  case class Ensuring(body: Expr, id: Identifier, pred: Expr) extends Expr {
    def getType = body.getType
  }

  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr {
    def getType = body.getType
  }

  case class Choose(vars: List[Identifier], pred: Expr, var impl: Option[Expr] = None) extends Expr with NAryExtractable {
    require(!vars.isEmpty)

    def getType = if (vars.size > 1) TupleType(vars.map(_.getType)) else vars.head.getType

    def extract = {
      Some((Seq(pred)++impl, (es: Seq[Expr]) =>  Choose(vars, es.head, es.tail.headOption).setPos(this)))
    }
  }

  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    def getType = body.getType
  }

  case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr {
    require(value.getType.isInstanceOf[TupleType],
           "The definition value in LetTuple must be of some tuple type; yet we got [%s]. In expr: \n%s".format(value.getType, this))

    def getType = body.getType
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    def getType = body.getType
  }

  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    def getType = tfd.returnType
  }

  /**
   * OO Trees
   *
   * Both MethodInvocation and This get removed by phase MethodLifting. Methods become functions,
   * This becomes first argument, and MethodInvocation become FunctionInvocation.
   */
  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr {
    def getType = {
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
    assert(caller.getType.isInstanceOf[FunctionType])
    def getType = caller.getType.asInstanceOf[FunctionType].to
  }

  case class Lambda(args: Seq[ValDef], body: Expr) extends Expr {
    def getType = FunctionType(args.map(_.tpe), body.getType)
  }

  object FiniteLambda {
    def unapply(lambda: Lambda): Option[(Expr, Seq[(Expr, Expr)])] = {
      val args = lambda.args.map(_.toVariable)
      lazy val argsTuple = if (lambda.args.size > 1) Tuple(args) else args.head

      def rec(body: Expr): Option[(Expr, Seq[(Expr, Expr)])] = body match {
        case _ : IntLiteral | _ : UMinus | _ : BooleanLiteral | _ : GenericValue | _ : Tuple |
             _ : CaseClass | _ : FiniteArray | _ : FiniteSet | _ : FiniteMap | _ : Lambda =>
          Some(body -> Seq.empty)
        case IfExpr(Equals(tpArgs, key), expr, elze) if tpArgs == argsTuple =>
          rec(elze).map { case (dflt, mapping) => dflt -> ((key -> expr) +: mapping) }
        case _ => None
      }

      rec(lambda.body)
    }

    def apply(dflt: Expr, els: Seq[(Expr, Expr)], tpe: FunctionType): Lambda = {
      val args = tpe.from.zipWithIndex.map { case (tpe, idx) =>
        ValDef(FreshIdentifier(s"x${idx + 1}").setType(tpe), tpe)
      }

      assert(els.isEmpty || !tpe.from.isEmpty, "Can't provide finite mapping for lambda without parameters")

      lazy val (tupleArgs, tupleKey) = if (tpe.from.size > 1) {
        val tpArgs = Tuple(args.map(_.toVariable))
        val key = (x: Expr) => x
        (tpArgs, key)
      } else { // note that value is lazy, so if tpe.from.size == 0, foldRight will never access (tupleArgs, tupleKey)
        val tpArgs = args.head.toVariable
        val key = (x: Expr) => {
          if (isSubtypeOf(x.getType, tpe.from.head)) x
          else if (isSubtypeOf(x.getType, TupleType(tpe.from))) x.asInstanceOf[Tuple].exprs.head
          else throw new RuntimeException("Can't determine key tuple state : " + x + " of " + tpe)
        }
        (tpArgs, key)
      }

      val body = els.toSeq.foldRight(dflt) { case ((k, v), elze) =>
        IfExpr(Equals(tupleArgs, tupleKey(k)), v, elze)
      }

      Lambda(args, body)
    }
  }

  case class Forall(args: Seq[ValDef], body: Expr) extends Expr {
    assert(body.getType == BooleanType)
    def getType = BooleanType
  }

  case class This(ct: ClassType) extends Expr with Terminal {
    def getType = ct
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    def getType = leastUpperBound(thenn.getType, elze.getType).getOrElse(Untyped)
  }

  case class Tuple(exprs: Seq[Expr]) extends Expr {
    def getType = TupleType(exprs.map(_.getType))
  }

  // Index is 1-based, first element of tuple is 1.
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    require(index >= 1)

    def getType = tuple.getType match {
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
    def getType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse(Untyped)
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
    def getType = BooleanType

    require(exprs.size >= 2)
  }

  object And {
    def apply(a: Expr, b: Expr): Expr = And(Seq(a, b))
  }

  case class Or(exprs: Seq[Expr]) extends Expr {
    def getType = BooleanType

    require(exprs.size >= 2)
  }

  object Or {
    def apply(a: Expr, b: Expr): Expr = Or(Seq(a, b))
  }

  case class Implies(lhs: Expr, rhs: Expr) extends Expr {
    def getType = BooleanType
  }

  case class Not(expr: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Equals(lhs: Expr, rhs: Expr) extends Expr {
    val getType = BooleanType
  }

  case class Variable(id: Identifier) extends Expr with Terminal {
    private var _tpe = id.getType

    def setType(tpe: TypeTree): this.type = {
      _tpe = tpe
      this
    }

    def getType = _tpe
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

  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] {
    val getType = BooleanType
  }

  case class StringLiteral(value: String) extends Literal[String] with MutableTyped

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
    def getType = classType.fieldsTypes(selectorIndex)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: CaseClassSelector => (t.classType, t.caseClass, t.selector) == (classType, caseClass, selector)
      case _ => false
    })

    override def hashCode: Int = (classType, caseClass, selector).hashCode + 9
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr {
    val getType = Int32Type
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class UMinus(expr: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr { 
    val getType = Int32Type
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

  /* Set expressions */
  case class FiniteSet(elements: Set[Expr]) extends Expr with MutableTyped {
    val tpe = if (elements.isEmpty) None else leastUpperBound(elements.toSeq.map(_.getType))
    tpe.filter(_ != Untyped).foreach(t => setType(SetType(t)))
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
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(set1, set2).map(_.getType)).getOrElse(Untyped)
  }

  /* Map operations. */
  case class FiniteMap(singletons: Seq[(Expr, Expr)]) extends Expr with MutableTyped
  case class MapGet(map: Expr, key: Expr) extends Expr {
    def getType = map.getType match {
      case MapType(from, to) => to
      case _ => Untyped
    }
  }
  case class MapUnion(map1: Expr, map2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(map1, map2).map(_.getType)).getOrElse(Untyped)
  }
  case class MapDifference(map: Expr, keys: Expr) extends Expr with MutableTyped
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr {
    val getType = BooleanType
  }


  /* Array operations */
  case class ArraySelect(array: Expr, index: Expr) extends Expr {
    def getType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        Untyped
    }
  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr {
    def getType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType(_)).getOrElse(Untyped)
      case _ =>
        Untyped
    }
  }

  case class ArrayLength(array: Expr) extends Expr {
    val getType = Int32Type
  }

  case class FiniteArray(elems: Map[Int, Expr], default: Option[Expr], length: Expr) extends Expr with MutableTyped

  object FiniteArray {
    def apply(elems: Seq[Expr]): FiniteArray = {
      val res = FiniteArray(elems.zipWithIndex.map(_.swap).toMap, None, IntLiteral(elems.size))
      elems.headOption.foreach(e => res.setType(ArrayType(e.getType)))
      res
    }
  }

  /* Special trees */

  // Provide an oracle (synthesizable, all-seeing choose)
  case class WithOracle(oracles: List[Identifier], body: Expr) extends Expr with UnaryExtractable {
    require(!oracles.isEmpty)

    def getType = body.getType

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
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr {
    def getType = ArrayType(defaultValue.getType)
  }

  case class SetMin(set: Expr) extends Expr {
    val getType = Int32Type
  }

  case class SetMax(set: Expr) extends Expr {
    val getType = Int32Type
  }

  case class EmptyMultiset(baseType: TypeTree) extends Expr with Terminal {
    val getType = MultisetType(baseType)
  }
  case class FiniteMultiset(elements: Seq[Expr]) extends Expr {
    require(elements.nonEmpty)
    def getType = MultisetType(leastUpperBound(elements.map(_.getType)).getOrElse(Untyped))
  }
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  case class MultisetCardinality(multiset: Expr) extends Expr {
    val getType = Int32Type
  }
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr  {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr { // disjoint union 
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr  {
    def getType = leastUpperBound(Seq(multiset1, multiset2).map(_.getType)).getOrElse(Untyped)
  }
  case class MultisetToSet(multiset: Expr) extends Expr {
    def getType = multiset.getType match {
      case MultisetType(base) => SetType(base)
      case _ => Untyped
    }
  }


}
