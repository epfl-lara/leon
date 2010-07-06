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

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val et = body.getType
    if(et != NoType)
      setType(et)
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
  object And {
    def apply(exprs: Seq[Expr]) : And = new And(exprs)

    def apply(l: Expr, r: Expr): Expr = (l,r) match {
      case (And(exs1), And(exs2)) => And(exs1 ++ exs2)
      case (And(exs1), ex2) => And(exs1 :+ ex2)
      case (ex1, And(exs2)) => And(exs2 :+ ex1)
      case (ex1, ex2) => And(List(ex1, ex2))
    }

    def unapply(and: And) : Option[Seq[Expr]] = 
        if(and == null) None else Some(and.exprs)
  }

  class And(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  object Or {
    def apply(exprs: Seq[Expr]) : Or = new Or(exprs)

    def apply(l: Expr, r: Expr): Expr = (l,r) match {
      case (Or(exs1), Or(exs2)) => Or(exs1 ++ exs2)
      case (Or(exs1), ex2) => Or(exs1 :+ ex2)
      case (ex1, Or(exs2)) => Or(exs2 :+ ex1)
      case (ex1, ex2) => Or(List(ex1, ex2))
    }

    def unapply(or: Or) : Option[Seq[Expr]] = 
        if(or == null) None else Some(or.exprs)
  }

  class Or(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  case class Iff(left: Expr, right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  case class Implies(left: Expr, right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  case class Not(expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* For all types that don't have their own XXXEquals */
  case class Equals(left: Expr, right: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
  
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

  case class IntLiteral(value: Int) extends Literal[Int] with FixedType {
    val fixedType = Int32Type
  }
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] with FixedType {
    val fixedType = BooleanType
  }
  case class StringLiteral(value: String) extends Literal[String]

  case class CaseClass(classDef: CaseClassDef, args: Seq[Expr]) extends Expr
  case class CaseClassSelector(caseClass: Expr, selector: Identifier) extends Expr

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

  /* Option expressions */
  case class OptionSome(value: Expr) extends Expr 
  case class OptionNone(baseType: TypeTree) extends Expr 

  /* Set expressions */
  case class EmptySet(baseType: TypeTree) extends Expr 
  case class FiniteSet(elements: Seq[Expr]) extends Expr 
  case class ElementOfSet(element: Expr, set: Expr) extends Expr 
  case class IsEmptySet(set: Expr) extends Expr 
  case class SetEquals(set1: Expr, set2: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr 
  case class SetIntersection(set1: Expr, set2: Expr) extends Expr 
  case class SetUnion(set1: Expr, set2: Expr) extends Expr 
  case class SetDifference(set1: Expr, set2: Expr) extends Expr 
  case class SetMin(set: Expr) extends Expr
  case class SetMax(set: Expr) extends Expr

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
  case class MapDifference(map: Expr, keys: Expr) extends Expr 

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr 
  case class Cons(head: Expr, tail: Expr) extends Expr 
  case class Car(list: Expr) extends Expr 
  case class Cdr(list: Expr) extends Expr 
  case class Concat(list1: Expr, list2: Expr) extends Expr 
  case class ListAt(list: Expr, index: Expr) extends Expr 

  object UnaryOperator {
    def unapply(expr: Expr) : Option[(Expr,(Expr)=>Expr)] = expr match {
      case IsEmptySet(t) => Some((t,IsEmptySet))
      case SetCardinality(t) => Some((t,SetCardinality))
      case Car(t) => Some((t,Car))
      case Cdr(t) => Some((t,Cdr))
      case _ => None
    }
  }

  object BinaryOperator {
    def unapply(expr: Expr) : Option[(Expr,Expr,(Expr,Expr)=>Expr)] = expr match {
      case Equals(t1,t2) => Some((t1,t2,Equals))
      case Iff(t1,t2) => Some((t1,t2,Iff))
      case Implies(t1,t2) => Some((t1,t2,Implies))
      case Plus(t1,t2) => Some((t1,t2,Plus))
      case Minus(t1,t2) => Some((t1,t2,Minus))
      case Times(t1,t2) => Some((t1,t2,Times))
      case Division(t1,t2) => Some((t1,t2,Division))
      case LessThan(t1,t2) => Some((t1,t2,LessThan))
      case GreaterThan(t1,t2) => Some((t1,t2,GreaterThan))
      case LessEquals(t1,t2) => Some((t1,t2,LessEquals))
      case GreaterEquals(t1,t2) => Some((t1,t2,GreaterEquals))
      case ElementOfSet(t1,t2) => Some((t1,t2,ElementOfSet))
      case SetEquals(t1,t2) => Some((t1,t2,SetEquals))
      case SubsetOf(t1,t2) => Some((t1,t2,SubsetOf))
      case SetIntersection(t1,t2) => Some((t1,t2,SetIntersection))
      case SetUnion(t1,t2) => Some((t1,t2,SetUnion))
      case SetDifference(t1,t2) => Some((t1,t2,SetDifference))
      case SingletonMap(t1,t2) => Some((t1,t2,SingletonMap))
      case MapGet(t1,t2) => Some((t1,t2,MapGet))
      case MapUnion(t1,t2) => Some((t1,t2,MapUnion))
      case MapDifference(t1,t2) => Some((t1,t2,MapDifference))
      case Concat(t1,t2) => Some((t1,t2,Concat))
      case ListAt(t1,t2) => Some((t1,t2,ListAt))
      case _ => None
    }
  }

  def negate(expr: Expr) : Expr = expr match {
    case Let(i,b,e) => Let(i,b,negate(e))
    case Not(e) => e
    case Iff(e1,e2) => Iff(negate(e1),e2)
    case Implies(e1,e2) => And(e1, negate(e2))
    case Or(exs) => And(exs.map(negate(_)))
    case And(exs) => Or(exs.map(negate(_)))
    case LessThan(e1,e2) => GreaterEquals(e1,e2)
    case LessEquals(e1,e2) => GreaterThan(e1,e2)
    case GreaterThan(e1,e2) => LessEquals(e1,e2)
    case GreaterEquals(e1,e2) => LessThan(e1,e2)
    case i @ IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2)).setType(i.getType)
    case _ => Not(expr)
  }
 
  // Warning ! This may loop forever if the substitutions are not
  // well-formed!
  def replace(substs: Map[Expr,Expr], expr: Expr) : Expr = {
    searchAndApply(substs.isDefinedAt(_), substs(_), expr)
  }

  // the replacement map should be understood as follows:
  //   - on each subexpression, checkFun checks whether it should be replaced
  //   - repFun is applied is checkFun succeeded
  def searchAndApply(checkFun: Expr=>Boolean, repFun: Expr=>Expr, expr: Expr) : Expr = {
    def rec(ex: Expr, skip: Expr = null) : Expr = ex match {
      case _ if (ex != skip && checkFun(ex)) => {
        val newExpr = repFun(ex)
        if(newExpr.getType == NoType) {
          Settings.reporter.warning("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
        }
        if(ex == newExpr)
          rec(ex, ex)
        else
          rec(newExpr)
      }
      case l @ Let(i,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        if(re != e || rb != b)
          Let(i, re, rb).setType(l.getType)
        else
          l
      }
      case f @ FunctionInvocation(fd, args) => {
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a)
          if(ra != a) {
            change = true  
            ra
          } else {
            a
          }            
        })
        if(change)
          FunctionInvocation(fd, rargs).setType(f.getType)
        else
          f
      }
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1),rec(t2),rec(t3)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType)
      case And(exs) => And(exs.map(rec(_)))
      case Or(exs) => Or(exs.map(rec(_)))
      case Not(e) => Not(rec(e))
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t)
        if(r != t)
          recons(r).setType(u.getType)
        else
          u
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        if(r1 != t1 || r2 != t2)
          recons(r1,r2).setType(b.getType)
        else
          b
      }
      case c @ CaseClass(cd, args) => {
        CaseClass(cd, args.map(rec(_))).setType(c.getType)
      }
      case c @ CaseClassSelector(cc, sel) => {
        val rc = rec(cc)
        if(rc != cc)
          CaseClassSelector(rc, sel).setType(c.getType)
        else
          c
      }
      case _ => ex
    }

    def inCase(cse: MatchCase) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  /* Simplifies let expressions:
   *  - removes lets when expression never occurs
   *  - simplifies when expressions occurs exactly once
   * Note that the code is simple but far from optimal (many traversals...)
   */
  def simplifyLets(expr: Expr) : Expr = {
    val isLet = ((t: Expr) => t.isInstanceOf[Let])
    def simplerLet(t: Expr) : Expr = t match {
      case letExpr @ Let(i,e,b) => {
        var occurences = 0
        def isOcc(tr: Expr) = (occurences < 2 && tr.isInstanceOf[Variable] && tr.asInstanceOf[Variable].id == i)
        def incCount(tr: Expr) = { occurences = occurences + 1; tr } 
        searchAndApply(isOcc,incCount,b)
        if(occurences == 0) {
          b
        } else if(occurences == 1) {
          expandLets(letExpr)
        } else {
          t
        }
      }
      case o => o
    }
    searchAndApply(isLet,simplerLet,expr)
  }

  /* Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case f @ FunctionInvocation(fd, args) => FunctionInvocation(fd, args.map(rec(_, s))).setType(f.getType)
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut, s), cses.map(inCase(_, s))).setType(m.getType)
      case And(exs) => And(exs.map(rec(_, s)))
      case Or(exs) => Or(exs.map(rec(_, s)))
      case Not(e) => Not(rec(e, s))
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t, s)
        if(r != t)
          recons(r).setType(u.getType)
        else
          u
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1, s)
        val r2 = rec(t2, s)
        if(r1 != t1 || r2 != t2)
          recons(r1,r2).setType(b.getType)
        else
          b
      }
      case c @ CaseClass(cd, args) => {
        CaseClass(cd, args.map(rec(_, s))).setType(c.getType)
      }
      case c @ CaseClassSelector(cc, sel) => {
        val rc = rec(cc, s)
        if(rc != cc)
          CaseClassSelector(rc, sel).setType(c.getType)
        else
          c
      }
      case _ => ex
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs, s))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard, s), rec(rhs, s))
    }

    rec(expr, Map.empty)
  }
}
