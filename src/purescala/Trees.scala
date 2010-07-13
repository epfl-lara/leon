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

  sealed trait Terminal

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    val et = body.getType
    if(et != NoType)
      setType(et)
  }

  /* Control flow */
  case class FunctionInvocation(funDef: FunDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = funDef.returnType
  }
  case class IfExpr(cond: Expr, then: Expr, elze: Expr) extends Expr 
  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr {
    def scrutineeClassType: ClassType = scrutinee.getType.asInstanceOf[ClassType]
  }

  sealed abstract class MatchCase {
    val pattern: Pattern
    val rhs: Expr
    val theGuard: Option[Expr]
    def hasGuard = theGuard.isDefined
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
    def apply(exprs: Seq[Expr]) : Expr = exprs.size match {
      case 0 => BooleanLiteral(true)
      case 1 => exprs.head
      case _ => new And(exprs)
    }

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
    def apply(exprs: Seq[Expr]) : Expr = exprs.size match {
      case 0 => BooleanLiteral(false)
      case 1 => exprs.head
      case _ => new Or(exprs)
    }

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
  }

  case class Not(expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* For all types that don't have their own XXXEquals */
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
  }
  
  case class Variable(id: Identifier) extends Expr with Terminal {
    override def getType = id.getType
    override def setType(tt: TypeTree) = { id.setType(tt); this }
  }

  // represents the result in post-conditions
  case class ResultVariable() extends Expr with Terminal

  /* Literals */
  sealed abstract class Literal[T] extends Expr with Terminal {
    val value: T
  }

  case class IntLiteral(value: Int) extends Literal[Int] with FixedType {
    val fixedType = Int32Type
  }
  case class BooleanLiteral(value: Boolean) extends Literal[Boolean] with FixedType {
    val fixedType = BooleanType
  }
  case class StringLiteral(value: String) extends Literal[String]

  case class CaseClass(classDef: CaseClassDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = CaseClassType(classDef)
  }
  case class CaseClassSelector(caseClass: Expr, selector: Identifier) extends Expr with FixedType {
    val fixedType = caseClass.getType.asInstanceOf[CaseClassType].classDef.fields.find(_.id == selector).get.getType
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
  case class OptionNone(baseType: TypeTree) extends Expr with Terminal

  /* Set expressions */
  case class EmptySet(baseType: TypeTree) extends Expr with Terminal
  case class FiniteSet(elements: Seq[Expr]) extends Expr 
  case class ElementOfSet(element: Expr, set: Expr) extends Expr 
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
  case class EmptyMap(fromType: TypeTree, toType: TypeTree) extends Expr with Terminal
  case class SingletonMap(from: Expr, to: Expr) extends Expr 
  case class FiniteMap(singletons: Seq[SingletonMap]) extends Expr 

  case class MapGet(map: Expr, key: Expr) extends Expr 
  case class MapUnion(map1: Expr, map2: Expr) extends Expr 
  case class MapDifference(map: Expr, keys: Expr) extends Expr 

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr with Terminal
  case class Cons(head: Expr, tail: Expr) extends Expr 
  case class Car(list: Expr) extends Expr 
  case class Cdr(list: Expr) extends Expr 
  case class Concat(list1: Expr, list2: Expr) extends Expr 
  case class ListAt(list: Expr, index: Expr) extends Expr 

  object UnaryOperator {
    def unapply(expr: Expr) : Option[(Expr,(Expr)=>Expr)] = expr match {
      case Not(t) => Some((t,Not(_)))
      case SetCardinality(t) => Some((t,SetCardinality))
      case MultisetCardinality(t) => Some((t,MultisetCardinality))
      case MultisetToSet(t) => Some((t,MultisetToSet))
      case Car(t) => Some((t,Car))
      case Cdr(t) => Some((t,Cdr))
      case SetMin(s) => Some((s,SetMin))
      case SetMax(s) => Some((s,SetMax))
      case CaseClassSelector(e, sel) => Some((e, CaseClassSelector(_, sel)))
      case _ => None
    }
  }

  object BinaryOperator {
    def unapply(expr: Expr) : Option[(Expr,Expr,(Expr,Expr)=>Expr)] = expr match {
      case Equals(t1,t2) => Some((t1,t2,Equals.apply))
      case Iff(t1,t2) => Some((t1,t2,Iff))
      case Implies(t1,t2) => Some((t1,t2,Implies.apply))
      case Plus(t1,t2) => Some((t1,t2,Plus))
      case Minus(t1,t2) => Some((t1,t2,Minus))
      case Times(t1,t2) => Some((t1,t2,Times))
      case Division(t1,t2) => Some((t1,t2,Division))
      case LessThan(t1,t2) => Some((t1,t2,LessThan))
      case GreaterThan(t1,t2) => Some((t1,t2,GreaterThan))
      case LessEquals(t1,t2) => Some((t1,t2,LessEquals))
      case GreaterEquals(t1,t2) => Some((t1,t2,GreaterEquals))
      case ElementOfSet(t1,t2) => Some((t1,t2,ElementOfSet))
      case SubsetOf(t1,t2) => Some((t1,t2,SubsetOf))
      case SetIntersection(t1,t2) => Some((t1,t2,SetIntersection))
      case SetUnion(t1,t2) => Some((t1,t2,SetUnion))
      case SetDifference(t1,t2) => Some((t1,t2,SetDifference))
      case Multiplicity(t1,t2) => Some((t1,t2,Multiplicity))
      case SubmultisetOf(t1,t2) => Some((t1,t2,SubmultisetOf))
      case MultisetIntersection(t1,t2) => Some((t1,t2,MultisetIntersection))
      case MultisetUnion(t1,t2) => Some((t1,t2,MultisetUnion))
      case MultisetPlus(t1,t2) => Some((t1,t2,MultisetPlus))
      case MultisetDifference(t1,t2) => Some((t1,t2,MultisetDifference))
      case SingletonMap(t1,t2) => Some((t1,t2,SingletonMap))
      case MapGet(t1,t2) => Some((t1,t2,MapGet))
      case MapUnion(t1,t2) => Some((t1,t2,MapUnion))
      case MapDifference(t1,t2) => Some((t1,t2,MapDifference))
      case Concat(t1,t2) => Some((t1,t2,Concat))
      case ListAt(t1,t2) => Some((t1,t2,ListAt))
      case _ => None
    }
  }

  object NAryOperator {
    def unapply(expr: Expr) : Option[(Seq[Expr],(Seq[Expr])=>Expr)] = expr match {
      case FunctionInvocation(fd, args) => Some((args, FunctionInvocation(fd, _)))
      case CaseClass(cd, args) => Some((args, CaseClass(cd, _)))
      case And(args) => Some((args, And.apply))
      case Or(args) => Some((args, Or.apply))
      case FiniteSet(args) => Some((args, FiniteSet))
      case FiniteMultiset(args) => Some((args, FiniteMultiset))
      case _ => None
    }
  }

  def negate(expr: Expr) : Expr = expr match {
    case Let(i,b,e) => Let(i,b,negate(e))
    case Not(e) => e
    case Iff(e1,e2) => Iff(negate(e1),e2)
    case Implies(e1,e2) => And(e1, negate(e2))
    case Or(exs) => And(exs map negate)
    case And(exs) => Or(exs map negate)
    case LessThan(e1,e2) => GreaterEquals(e1,e2)
    case LessEquals(e1,e2) => GreaterThan(e1,e2)
    case GreaterThan(e1,e2) => LessEquals(e1,e2)
    case GreaterEquals(e1,e2) => LessThan(e1,e2)
    case i @ IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2)).setType(i.getType)
    case BooleanLiteral(b) => BooleanLiteral(!b)
    case _ => Not(expr)
  }
 
  // Warning ! This may loop forever if the substitutions are not
  // well-formed!
  def replace(substs: Map[Expr,Expr], expr: Expr) : Expr = {
    searchAndReplace(substs.get)(expr)
  }

  def searchAndReplace(subst: Expr=>Option[Expr], recursive: Boolean=true)(expr: Expr) : Expr = {
    def rec(ex: Expr, skip: Expr = null) : Expr = (if (ex == skip) None else subst(ex)) match {
      case Some(newExpr) => {
        if(newExpr.getType == NoType) {
          Settings.reporter.warning("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
        }
        if(ex == newExpr)
          if(recursive) rec(ex, ex) else ex
        else
          if(recursive) rec(newExpr) else newExpr
      }
      case None => ex match {
        case l @ Let(i,e,b) => {
          val re = rec(e)
          val rb = rec(b)
          if(re != e || rb != b)
            Let(i, re, rb).setType(l.getType)
          else
            l
        }
        case n @ NAryOperator(args, recons) => {
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
            recons(rargs).setType(n.getType)
          else
            n
        }
        case b @ BinaryOperator(t1,t2,recons) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          if(r1 != t1 || r2 != t2)
            recons(r1,r2).setType(b.getType)
          else
            b
        }
        case u @ UnaryOperator(t,recons) => {
          val r = rec(t)
          if(r != t)
            recons(r).setType(u.getType)
          else
            u
        }
        case i @ IfExpr(t1,t2,t3) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          val r3 = rec(t3)
          if(r1 != t1 || r2 != t2 || r3 != t3)
            IfExpr(rec(t1),rec(t2),rec(t3)).setType(i.getType)
          else
            i
        }
        case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType)
        case t if t.isInstanceOf[Terminal] => t
        case unhandled => scala.Predef.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
      }
    }

    def inCase(cse: MatchCase) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  def variablesOf(expr: Expr) : Set[Identifier] = {
    def rec(ex: Expr, lets: Set[Identifier]) : Set[Identifier] = ex match {
      case l @ Let(i,e,b) => {
        val newLets = lets + i
        rec(e, newLets) ++ rec(b, newLets)
      }
      case Variable(i) => if(lets(i)) Set.empty[Identifier] else Set(i)
      case n @ NAryOperator(args, _) => if(args.isEmpty) Set.empty[Identifier] else args.map(rec(_, lets)).reduceLeft(_ ++ _)
      case b @ BinaryOperator(t1,t2,_) => rec(t1,lets) ++ rec(t2,lets)
      case u @ UnaryOperator(t,_) => rec(t, lets)
      case i @ IfExpr(t1,t2,t3) => rec(t1,lets) ++ rec(t2,lets) ++ rec(t3,lets)
      case m @ MatchExpr(scrut,cses) => rec(scrut, lets) ++ cses.map(inCase(_, lets)).reduceLeft(_ ++ _)
      case t if t.isInstanceOf[Terminal] => Set.empty[Identifier]
      case unhandled => scala.Predef.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
    }

    // note that the identifiers in the patterns are not included if they don't show up on the rhs.
    def inCase(cse: MatchCase, lets: Set[Identifier]) : Set[Identifier] = cse match {
      case SimpleCase(pat, rhs) => rec(rhs, lets)
      case GuardedCase(pat, guard, rhs) => rec(guard, lets) ++ rec(rhs, lets)
    }

    rec(expr, Set.empty)
  }

  /* Simplifies let expressions:
   *  - removes lets when expression never occurs
   *  - simplifies when expressions occurs exactly once
   *  - expands when expression is just a variable.
   * Note that the code is simple but far from optimal (many traversals...)
   */
  def simplifyLets(expr: Expr) : Expr = {
    def simplerLet(t: Expr) : Option[Expr] = t match {
      case letExpr @ Let(i, Variable(v), b) => Some(replace(Map((Variable(i) -> Variable(v))), b))
      case letExpr @ Let(i, l: Literal[_], b) => Some(replace(Map((Variable(i) -> l)), b))
      case letExpr @ Let(i,e,b) => {
        var occurences = 0
        def incCount(tr: Expr) = tr match {
          case Variable(x) if x == i => { occurences = occurences + 1; None } 
          case _ => None
        }
        searchAndReplace(incCount, false)(b)
        if(occurences == 0) {
          Some(b)
        } else if(occurences == 1) {
          Some(replace(Map((Variable(i) -> e)), b))
        } else {
          None
        }
      }
      case _ => None 
    }
    searchAndReplace(simplerLet)(expr)
  }

  /* Rewrites the expression so that all lets are at the top levels. */
  def pulloutLets(expr: Expr) : Expr = {
    val (storedLets, noLets) = pulloutAndKeepLets(expr)
    rebuildLets(storedLets, noLets)
  }
  
  // new code (keep this if nested lets can appear in the value part, too)
  def pulloutAndKeepLets(expr: Expr) : (List[(Identifier,Expr)], Expr) = {
    var storedLets: List[(Identifier,Expr)] = Nil

    def storeLet(t: Expr) : Option[Expr] = t match {
      case l @ Let(i, e, b) =>
        val (stored, value) = pulloutAndKeepLets(e)
        storedLets :::= stored
        storedLets ::= i -> value
        Some(b)
      case _ => None
    }
    val noLets = searchAndReplace(storeLet)(expr)
    (storedLets, noLets)
  }

  def rebuildLets(lets: Seq[(Identifier,Expr)], expr: Expr) : Expr = {
    lets.foldLeft(expr)((e,p) => Let(p._1, p._2, e))
  }

  /* Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut, s), cses.map(inCase(_, s))).setType(m.getType)
      case n @ NAryOperator(args, recons) => {
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a, s)
          if(ra != a) {
            change = true  
            ra
          } else {
            a
          }            
        })
        if(change)
          recons(rargs).setType(n.getType)
        else
          n
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1, s)
        val r2 = rec(t2, s)
        if(r1 != t1 || r2 != t2)
          recons(r1,r2).setType(b.getType)
        else
          b
      }
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t, s)
        if(r != t)
          recons(r).setType(u.getType)
        else
          u
      }
      case t if t.isInstanceOf[Terminal] => t
      case unhandled => scala.Predef.error("Unhandled case in expandLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs, s))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard, s), rec(rhs, s))
    }

    rec(expr, Map.empty)
  }

  object SimplePatternMatching {
    // (scrutinee, classtype, list((caseclassdef, variable, list(variable), rhs)))
    def unapply(e: MatchExpr) : Option[(Expr,ClassType,Seq[(CaseClassDef,Identifier,Seq[Identifier],Expr)])] = {
      val MatchExpr(scrutinee, cases) = e
      val sType = scrutinee.getType

      if(sType.isInstanceOf[AbstractClassType]) {
        val cCD = sType.asInstanceOf[AbstractClassType].classDef
        if(cases.size == cCD.knownChildren.size && cases.forall(!_.hasGuard)) {
          var seen = Set.empty[ClassTypeDef]
          
          var lle : List[(CaseClassDef,Identifier,List[Identifier],Expr)] = Nil
          for(cse <- cases) {
            cse match {
              case SimpleCase(CaseClassPattern(binder, ccd, subPats), rhs) if subPats.forall(_.isInstanceOf[WildcardPattern]) => {
                seen = seen + ccd

                val patID : Identifier = if(binder.isDefined) {
                  binder.get
                } else {
                  FreshIdentifier("cse", true).setType(CaseClassType(ccd))
                }

                val argIDs : List[Identifier] = (ccd.fields zip subPats.map(_.asInstanceOf[WildcardPattern])).map(p => if(p._2.binder.isDefined) {
                  p._2.binder.get
                } else {
                  FreshIdentifier("pat", true).setType(p._1.tpe)
                }).toList

                lle = (ccd, patID, argIDs, rhs) :: lle
              }
              case _ => ;
            }
          }
          lle = lle.reverse

          if(seen.size == cases.size) {
            Some((scrutinee, sType.asInstanceOf[AbstractClassType], lle))
          } else {
            None
          }
        } else {
          None
        }
      } else {
        val cCD = sType.asInstanceOf[CaseClassType].classDef
        if(cases.size == 1 && !cases(0).hasGuard) {
          val SimpleCase(pat,rhs) = cases(0).asInstanceOf[SimpleCase]
          pat match {
            case CaseClassPattern(binder, ccd, subPats) if (ccd == cCD && subPats.forall(_.isInstanceOf[WildcardPattern])) => {
              val patID : Identifier = if(binder.isDefined) {
                binder.get
              } else {
                FreshIdentifier("cse", true).setType(CaseClassType(ccd))
              }

              val argIDs : List[Identifier] = (ccd.fields zip subPats.map(_.asInstanceOf[WildcardPattern])).map(p => if(p._2.binder.isDefined) {
                p._2.binder.get
              } else {
                FreshIdentifier("pat", true).setType(p._1.tpe)
              }).toList

              Some((scrutinee, CaseClassType(cCD), List((cCD, patID, argIDs, rhs))))
            }
            case _ => None
          }
        } else {
          None
        }
      }
    }
  }

  object NotSoSimplePatternMatching {
    def coversType(tpe: ClassTypeDef, patterns: Seq[Pattern]) : Boolean = {
      if(patterns.isEmpty) {
        false
      } else if(patterns.exists(_.isInstanceOf[WildcardPattern])) {
        true
      } else {
        val allSubtypes: Seq[CaseClassDef] = tpe match {
          case acd @ AbstractClassDef(_,_) => acd.knownDescendents.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])
          case ccd: CaseClassDef => List(ccd)
        }

        var seen: Set[CaseClassDef] = Set.empty
        var secondLevel: Map[(CaseClassDef,Int),List[Pattern]] = Map.empty

        for(pat <- patterns) if (pat.isInstanceOf[CaseClassPattern]) {
          val pattern: CaseClassPattern = pat.asInstanceOf[CaseClassPattern]
          val ccd: CaseClassDef = pattern.caseClassDef
          seen = seen + ccd

          for((subPattern,i) <- (pattern.subPatterns.zipWithIndex)) {
            val seenSoFar = secondLevel.getOrElse((ccd,i), Nil)
            secondLevel = secondLevel + ((ccd,i) -> (subPattern :: seenSoFar))
          }
        }

        allSubtypes.forall(ccd => {
          seen(ccd) && ccd.fields.zipWithIndex.forall(p => p._1.tpe match {
            case t: ClassType => coversType(t.classDef, secondLevel.getOrElse((ccd, p._2), Nil))
            case _ => true
          })
        })
      }
    }

    def unapply(pm : MatchExpr) : Option[MatchExpr] = if(!Settings.experimental) None else (pm match {
      case MatchExpr(scrutinee, cases) if cases.forall(_.isInstanceOf[SimpleCase]) => {
        val allPatterns = cases.map(_.pattern)
        Settings.reporter.info("This might be a complete pattern-matching expression:")
        Settings.reporter.info(pm)
        Settings.reporter.info("Covered? " + coversType(pm.scrutineeClassType.classDef, allPatterns))
        None
      }
      case _ => None
    })
  }

  // we use this when debugging our tree transformations...
  def wellOrderedLets(tree : Expr) : Boolean = {
    val (pairs, _) = pulloutAndKeepLets(tree)
    val definitions: Set[Identifier] = Set(pairs.map(_._1) : _*)
    val vars: Set[Identifier] = variablesOf(tree)
    val intersection = vars intersect definitions
    if(intersection.isEmpty) true
    else {
      intersection.foreach(id => {
        Settings.reporter.error("Variable with identifier '" + id + "' has escaped its let-definition !")
      })
      false
    }
  }
}
