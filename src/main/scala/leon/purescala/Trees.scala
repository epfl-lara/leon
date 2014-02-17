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


  /* EXPRESSIONS */
  abstract class Expr extends Tree with Typed with Serializable

  trait Terminal {
    self: Expr =>
  }

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(description: String) extends Expr with Terminal

  case class Choose(vars: List[Identifier], pred: Expr) extends Expr with FixedType with UnaryExtractable {

    assert(!vars.isEmpty)

    val fixedType = if (vars.size > 1) TupleType(vars.map(_.getType)) else vars.head.getType

    def extract = {
      Some((pred, (e: Expr) => Choose(vars, e).setPos(this)))
    }
  }

  // A hole is like a all-seeing choose
  case class Hole(oracle: Expr) extends Expr with UnaryExtractable {
    def extract = {
      Some((oracle, (o: Expr) => Hole(o).copiedFrom(this)))
    }
  }

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr with FixedType {
    val fixedType = body.getType
  }

  case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr with FixedType {
    assert(value.getType.isInstanceOf[TupleType],
           "The definition value in LetTuple must be of some tuple type; yet we got [%s]. In expr: \n%s".format(value.getType, this))

    val fixedType = body.getType
  }

  case class LetDef(fd: FunDef, body: Expr) extends Expr {
    val et = body.getType
    if(et != Untyped)
      setType(et)

  }


  /* Control flow */
  case class FunctionInvocation(tfd: TypedFunDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = tfd.returnType
  }

  case class MethodInvocation(rec: Expr, cd: ClassDef, tfd: TypedFunDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = {
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

  case class This(ct: ClassType) extends Expr with FixedType with Terminal {
    val fixedType = ct
  }

  case class IfExpr(cond: Expr, thenn: Expr, elze: Expr) extends Expr with FixedType {
    val fixedType = leastUpperBound(thenn.getType, elze.getType).getOrElse{
      Untyped
    }
  }
  /* a construct for assuming a condition at a specific point in the body*/
  case class Assume(cond: Expr) extends Expr with FixedType {
    val fixedType = UnitType
  }
  
  case class Tuple(exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = TupleType(exprs.map(_.getType))
  }

  object TupleSelect {
    def apply(tuple: Expr, index: Int): Expr = {
      tuple match {
        case Tuple(exprs) => exprs(index-1) // indexes as 1-based
        case _ => new TupleSelect(tuple, index)
      }
    }

    def unapply(e: TupleSelect): Option[(Expr, Int)] = {
      if (e eq null) None else Some((e.tuple, e.index))
    }
  }

  // This must be 1-indexed ! (So are methods of Scala Tuples)
  class TupleSelect(val tuple: Expr, val index: Int) extends Expr with FixedType {
    assert(index >= 1)

    assert(tuple.getType.isInstanceOf[TupleType], "Applying TupleSelect on a non-tuple tree [%s] of type [%s].".format(tuple, tuple.getType))

    val fixedType : TypeTree = tuple.getType match {
      case TupleType(ts) =>
        assert(index <= ts.size)
        ts(index - 1)

      case _ =>
        Untyped
    }

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: TupleSelect => t.tuple == tuple && t.index == index
      case _ => false
    })

    override def hashCode: Int = tuple.hashCode + index.hashCode + 1
  }

  object MatchExpr {
    def apply(scrutinee: Expr, cases: Seq[MatchCase]) : MatchExpr = {
      scrutinee.getType match {
        case a: AbstractClassType => new MatchExpr(scrutinee, cases)
        case c: CaseClassType => new MatchExpr(scrutinee, cases.filter(_.pattern match {
          case CaseClassPattern(_, cct, _) if cct.classDef != c.classDef => false
          case _ => true
        }))
        case t: TupleType => new MatchExpr(scrutinee, cases)
        case _ => scala.sys.error("Constructing match expression on non-class type.")
      }
    }

    def unapply(me: MatchExpr) : Option[(Expr,Seq[MatchCase])] = if (me == null) None else Some((me.scrutinee, me.cases))
  }

  class MatchExpr(val scrutinee: Expr, val cases: Seq[MatchCase]) extends Expr with FixedType {
    assert(cases.nonEmpty)

    val fixedType = leastUpperBound(cases.map(_.rhs.getType)).getOrElse{
      Untyped
    }

    def scrutineeClassType: ClassType = scrutinee.getType.asInstanceOf[ClassType]

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: MatchExpr => t.scrutinee == scrutinee && t.cases == cases
      case _ => false
    })

    override def hashCode: Int = scrutinee.hashCode + cases.hashCode + 2
  }

  sealed abstract class MatchCase extends Tree {
    val pattern: Pattern
    val rhs: Expr
    val theGuard: Option[Expr]
    def hasGuard = theGuard.isDefined
    def expressions: Seq[Expr]
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase {
    val theGuard = None
    def expressions = List(rhs)
  }
  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    val theGuard = Some(guard)
    def expressions = List(guard, rhs)
  }

  sealed abstract class Pattern extends Tree {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.map(_.binders).foldLeft[Set[Identifier]](Set.empty)(_ ++ _)
    def binders: Set[Identifier] = subBinders ++ (if(binder.isDefined) Set(binder.get) else Set.empty)
  }

  case class InstanceOfPattern(binder: Option[Identifier], ct: ClassType) extends Pattern { // c: Class
    val subPatterns = Seq.empty
  }
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq.empty
  } 
  case class CaseClassPattern(binder: Option[Identifier], ct: CaseClassType, subPatterns: Seq[Pattern]) extends Pattern

  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern


  /* Propositional logic */
  object And {
    def apply(l: Expr, r: Expr) : Expr = And(Seq(l, r))

    def apply(exprs: Seq[Expr]) : Expr = {
      val flat = exprs.flatMap(_ match {
        case And(es) => es
        case o => Seq(o)
      })

      var stop = false
      val simpler = for(e <- flat if !stop && e != BooleanLiteral(true)) yield {
        if(e == BooleanLiteral(false)) stop = true
        e
      }

      simpler match {
        case Seq() => BooleanLiteral(true)
        case Seq(x) => x
        case _ => new And(simpler)
      }
    }

    def unapply(and: And) : Option[Seq[Expr]] = 
      if(and == null) None else Some(and.exprs)
  }

  class And private (val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType

    assert(exprs.size >= 2)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: And => t.exprs == exprs
      case _ => false
    })

    override def hashCode: Int = exprs.hashCode + 3
  }

  object Or {
    def apply(l: Expr, r: Expr) : Expr = (l,r) match {
      case (BooleanLiteral(true),_)  => BooleanLiteral(true)
      case (BooleanLiteral(false),_) => r
      case (_,BooleanLiteral(false)) => l
      case _ => new Or(Seq(l,r))
    }
    def apply(exprs: Seq[Expr]) : Expr = {
      val flat = exprs.flatMap(_ match {
        case Or(es) => es
        case o => Seq(o)
      })

      var stop = false
      val simpler = for(e <- flat if !stop && e != BooleanLiteral(false)) yield {
        if(e == BooleanLiteral(true)) stop = true
        e
      }

      simpler match {
        case Seq() => BooleanLiteral(false)
        case Seq(x) => x
        case _ => new Or(simpler)
      }
    }

    def unapply(or: Or) : Option[Seq[Expr]] = 
      if(or == null) None else Some(or.exprs)
  }

  class Or(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType

    assert(exprs.size >= 2)

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Or => t.exprs == exprs
      case _ => false
    })

    override def hashCode: Int = exprs.hashCode + 4
  }

  object Iff {
    def apply(left: Expr, right: Expr) : Expr = (left, right) match {
      case (BooleanLiteral(true), r) => r
      case (l, BooleanLiteral(true)) => l
      case (BooleanLiteral(false), r) => Not(r)
      case (l, BooleanLiteral(false)) => Not(l)
      case (l,r) => new Iff(l, r)  
    }

    def unapply(iff: Iff) : Option[(Expr,Expr)] = {
      if(iff != null) Some((iff.left, iff.right)) else None
    }
  }

  class Iff(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Iff => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode + right.hashCode + 5
  }

  object Implies {
    def apply(left: Expr, right: Expr) : Expr = (left,right) match {
      case (BooleanLiteral(false), _) => BooleanLiteral(true)
      case (_, BooleanLiteral(true)) => BooleanLiteral(true)
      case (BooleanLiteral(true), r) => r
      case (l, BooleanLiteral(false)) => Not(l)
      case (l1, Implies(l2, r2)) => Implies(And(l1, l2), r2)
      case _ => new Implies(left, right)
    }
    def unapply(imp: Implies) : Option[(Expr,Expr)] =
      if(imp == null) None else Some(imp.left, imp.right)
  }

  class Implies(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Implies => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode + right.hashCode + 6
  }

  object Not {
    def apply(expr : Expr) : Expr = expr match {
      case Not(e) => e
      case BooleanLiteral(v) => BooleanLiteral(!v)
      case _ => new Not(expr)
    }

    def unapply(not : Not) : Option[Expr] = {
      if(not != null) Some(not.expr) else None
    }
  }

  class Not private (val expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any) : Boolean = (that != null) && (that match {
      case n : Not => n.expr == expr
      case _ => false
    })

    override def hashCode : Int = expr.hashCode + 7
  }

  object Equals {
    def apply(l : Expr, r : Expr) : Expr = (l.getType, r.getType) match {
      case (BooleanType, BooleanType) => Iff(l, r)
      case _ => new Equals(l, r)
    }
    def unapply(e : Equals) : Option[(Expr,Expr)] = if (e == null) None else Some((e.left, e.right))
  }

  object SetEquals {
    def apply(l : Expr, r : Expr) : Equals = new Equals(l,r)
    def unapply(e : Equals) : Option[(Expr,Expr)] = if(e == null) None else (e.left.getType, e.right.getType) match {
      case (SetType(_), SetType(_)) => Some((e.left, e.right))
      case _ => None
    }
  }

  object MultisetEquals {
    def apply(l : Expr, r : Expr) : Equals = new Equals(l,r)
    def unapply(e : Equals) : Option[(Expr,Expr)] = if(e == null) None else (e.left.getType, e.right.getType) match {
      case (MultisetType(_), MultisetType(_)) => Some((e.left, e.right))
      case _ => None
    }
  }

  class Equals(val left: Expr, val right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: Equals => t.left == left && t.right == right
      case _ => false
    })

    override def hashCode: Int = left.hashCode + right.hashCode + 8
  }
  
  case class Variable(id: Identifier) extends Expr with Terminal {
    override def getType = id.getType
    override def setType(tt: TypeTree) = { id.setType(tt); this }
  }

  /* Literals */
  sealed abstract class Literal[T] extends Expr with Terminal {
    val value: T
  }

  case class GenericValue(tp: TypeParameter, id: Int) extends Expr with Terminal with FixedType {
    val fixedType = tp
  }

  case class IntLiteral(value: Int) extends Literal[Int] with FixedType {
    val fixedType = Int32Type
  }
  
  //The real constants allowed by the language are only rationals
  case class RealLiteral(numerator: Int, denominator: Int) extends Literal[(Int,Int)] with FixedType {    
    val value = (numerator,denominator)
    val fixedType = RealType 
    
    private var overflow = false
    def setOverflow =  {
      overflow = true
    }
    
    def hasOverflow = overflow
  }
  
  //a wrapper for real and interger literals (that are wholenumbers and not fractions)
  object WholeNumber{
    def apply(x: Int) : IntLiteral = IntLiteral(x)
    def unapply(e : Expr) : Option[Int] = e match {
      case IntLiteral(x) => Some(x)
      case RealLiteral(x,1) => Some(x)
      case _ => None
    }
  }

  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] with FixedType {
    val fixedType = BooleanType
  }

  case class StringLiteral(value: String) extends Literal[String]
  case class UnitLiteral() extends Literal[Unit] with FixedType {
    val fixedType = UnitType
    val value = ()
  } 

  case class CaseClass(ct: CaseClassType, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = ct
  }

  case class CaseClassInstanceOf(classType: CaseClassType, expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
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

  class CaseClassSelector(val classType: CaseClassType, val caseClass: Expr, val selector: Identifier) extends Expr with FixedType {
    val fixedType = classType.fieldsTypes(classType.classDef.selectorID2Index(selector))

    override def equals(that: Any): Boolean = (that != null) && (that match {
      case t: CaseClassSelector => (t.classType, t.caseClass, t.selector) == (classType, caseClass, selector)
      case _ => false
    })

    override def hashCode: Int = (classType, caseClass, selector).hashCode + 9
  }

  /* Arithmetic */
  case class Plus(lhs: Expr, rhs: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class Minus(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class UMinus(expr: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class Times(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class Division(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class Modulo(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = Int32Type
  }
  case class LessThan(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType
  }
  case class GreaterThan(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType
  }
  case class LessEquals(lhs: Expr, rhs: Expr) extends Expr with FixedType { 
    val fixedType = BooleanType
  }
  case class GreaterEquals(lhs: Expr, rhs: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* Set expressions */
  case class FiniteSet(elements: Seq[Expr]) extends Expr {
    val tpe = if (elements.isEmpty) None else leastUpperBound(elements.map(_.getType))
    tpe.foreach(t => setType(SetType(t)))
  }
  // TODO : Figure out what evaluation order is, for this.
  // Perhaps then rewrite as "contains".
  case class ElementOfSet(element: Expr, set: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  case class SetIntersection(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)
  }
  case class SetUnion(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)
  }
  case class SetDifference(set1: Expr, set2: Expr) extends Expr {
    leastUpperBound(Seq(set1, set2).map(_.getType)).foreach(setType _)
  }
  case class SetMin(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class SetMax(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }

  /* Multiset expressions */
  case class EmptyMultiset(baseType: TypeTree) extends Expr with Terminal
  case class FiniteMultiset(elements: Seq[Expr]) extends Expr 
  case class Multiplicity(element: Expr, multiset: Expr) extends Expr 
  case class MultisetCardinality(multiset: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class SubmultisetOf(multiset1: Expr, multiset2: Expr) extends Expr 
  case class MultisetIntersection(multiset1: Expr, multiset2: Expr) extends Expr 
  case class MultisetUnion(multiset1: Expr, multiset2: Expr) extends Expr 
  case class MultisetPlus(multiset1: Expr, multiset2: Expr) extends Expr // disjoint union
  case class MultisetDifference(multiset1: Expr, multiset2: Expr) extends Expr 
  case class MultisetToSet(multiset: Expr) extends Expr

  /* Map operations. */
  case class FiniteMap(singletons: Seq[(Expr, Expr)]) extends Expr {
    if (!singletons.isEmpty) {
      //compute the lub of all the key types and value types 
      val (keyTypes, valTypes) = singletons.foldLeft((Seq[TypeTree](), Seq[TypeTree]()))((acc, elem) => {
        val (ktpes, vtpes) = acc
        (ktpes :+ elem._1.getType, vtpes :+ elem._2.getType)
      })
      val keylub = TypeTrees.leastUpperBound(keyTypes)
      val vallub = TypeTrees.leastUpperBound(valTypes)
      if (keylub.isDefined && vallub.isDefined)
        this.setType(MapType(keylub.get, vallub.get))
    }
  }

  case class MapGet(map: Expr, key: Expr) extends Expr
  case class MapUnion(map1: Expr, map2: Expr) extends Expr 
  case class MapDifference(map: Expr, keys: Expr) extends Expr 
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* Array operations */
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr with FixedType {
    val fixedType = ArrayType(defaultValue.getType)
  }

  case class ArrayMake(defaultValue: Expr) extends Expr with FixedType {
    val fixedType = ArrayType(defaultValue.getType)
  }

  case class ArraySelect(array: Expr, index: Expr) extends Expr with FixedType {
    assert(array.getType.isInstanceOf[ArrayType],
           "The array value in ArraySelect must of of array type; yet we got [%s]. In expr: \n%s".format(array.getType, array))

    val fixedType = array.getType match {
      case ArrayType(base) =>
        base
      case _ =>
        Untyped
    }

  }

  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr with FixedType {
    assert(array.getType.isInstanceOf[ArrayType],
           "The array value in ArrayUpdated must of of array type; yet we got [%s]. In expr: \n%s".format(array.getType, array))

    val fixedType = array.getType match {
      case ArrayType(base) =>
        leastUpperBound(base, newValue.getType).map(ArrayType(_)).getOrElse(Untyped)
      case _ =>
        Untyped
    }
  }

  case class ArrayLength(array: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class FiniteArray(exprs: Seq[Expr]) extends Expr
  case class ArrayClone(array: Expr) extends Expr {
    if(array.getType != Untyped)
      setType(array.getType)
  }

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr with Terminal
  case class Cons(head: Expr, tail: Expr) extends Expr 
  case class Car(list: Expr) extends Expr 
  case class Cdr(list: Expr) extends Expr 
  case class Concat(list1: Expr, list2: Expr) extends Expr 
  case class ListAt(list: Expr, index: Expr) extends Expr 

  /* Constraint programming */
  case class Distinct(exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }

}
