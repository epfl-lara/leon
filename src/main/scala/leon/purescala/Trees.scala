package leon
package purescala

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import Definitions._

  /* EXPRESSIONS */

  sealed abstract class Expr extends Typed with Serializable {
    override def toString: String = PrettyPrinter(this)
  }

  sealed trait Terminal {
    self: Expr =>
  }

  case class Block(exprs: Seq[Expr], last: Expr) extends Expr {
    //val t = last.getType
    //if(t != Untyped)
     // setType(t)
  }

  case class Assignment(varId: Identifier, expr: Expr) extends Expr with FixedType {
    val fixedType = UnitType
  }
  case class While(cond: Expr, body: Expr) extends Expr with FixedType with ScalacPositional {
    val fixedType = UnitType
    var invariant: Option[Expr] = None

    def getInvariant: Expr = invariant.get
    def setInvariant(inv: Expr) = { invariant = Some(inv); this }
    def setInvariant(inv: Option[Expr]) = { invariant = inv; this }
  }

  /* This describes computational errors (unmatched case, taking min of an
   * empty set, division by zero, etc.). It should always be typed according to
   * the expected type. */
  case class Error(description: String) extends Expr with Terminal with ScalacPositional

  /* Like vals */
  case class Let(binder: Identifier, value: Expr, body: Expr) extends Expr {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)
  }
  //same as let, buf for mutable variable declaration
  case class LetVar(binder: Identifier, value: Expr, body: Expr) extends Expr {
    binder.markAsLetBinder
    val et = body.getType
    if(et != Untyped)
      setType(et)
  }

  //case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr {
  //  binders.foreach(_.markAsLetBinder)
  //  val et = body.getType
  //  if(et != Untyped)
  //    setType(et)
  //}

  case class LetDef(value: FunDef, body: Expr) extends Expr {
    val et = body.getType
    if(et != Untyped)
      setType(et)
  }

  /* Control flow */
  case class FunctionInvocation(funDef: FunDef, args: Seq[Expr]) extends Expr with FixedType with ScalacPositional {
    val fixedType = funDef.returnType
  }
  case class IfExpr(cond: Expr, then: Expr, elze: Expr) extends Expr 

  case class Tuple(exprs: Seq[Expr]) extends Expr
  case class TupleSelect(tuple: Expr, index: Int) extends Expr

  object MatchExpr {
    def apply(scrutinee: Expr, cases: Seq[MatchCase]) : MatchExpr = {
      scrutinee.getType match {
        case a: AbstractClassType => new MatchExpr(scrutinee, cases)
        case c: CaseClassType => new MatchExpr(scrutinee, cases.filter(_.pattern match {
          case CaseClassPattern(_, ccd, _) if ccd != c.classDef => false
          case _ => true
        }))
        case _ => scala.sys.error("Constructing match expression on non-class type.")
      }
    }

    def unapply(me: MatchExpr) : Option[(Expr,Seq[MatchCase])] = if (me == null) None else Some((me.scrutinee, me.cases))
  }

  class MatchExpr(val scrutinee: Expr, val cases: Seq[MatchCase]) extends Expr with ScalacPositional {
    def scrutineeClassType: ClassType = scrutinee.getType.asInstanceOf[ClassType]
  }

  sealed abstract class MatchCase extends Serializable {
    val pattern: Pattern
    val rhs: Expr
    val theGuard: Option[Expr]
    def hasGuard = theGuard.isDefined
    def expressions: Seq[Expr]

    def allIdentifiers : Set[Identifier] = {
      pattern.allIdentifiers ++ 
      Trees.allIdentifiers(rhs) ++ 
      theGuard.map(Trees.allIdentifiers(_)).getOrElse(Set[Identifier]()) ++ 
      (expressions map (Trees.allIdentifiers(_))).foldLeft(Set[Identifier]())((a, b) => a ++ b)
    }
  }

  case class SimpleCase(pattern: Pattern, rhs: Expr) extends MatchCase {
    val theGuard = None
    def expressions = List(rhs)
  }
  case class GuardedCase(pattern: Pattern, guard: Expr, rhs: Expr) extends MatchCase {
    val theGuard = Some(guard)
    def expressions = List(guard, rhs)
  }

  sealed abstract class Pattern extends Serializable {
    val subPatterns: Seq[Pattern]
    val binder: Option[Identifier]

    private def subBinders = subPatterns.map(_.binders).foldLeft[Set[Identifier]](Set.empty)(_ ++ _)
    def binders: Set[Identifier] = subBinders ++ (if(binder.isDefined) Set(binder.get) else Set.empty)

    def allIdentifiers : Set[Identifier] = {
      ((subPatterns map (_.allIdentifiers)).foldLeft(Set[Identifier]())((a, b) => a ++ b))  ++ binders
    }
  }
  case class InstanceOfPattern(binder: Option[Identifier], classTypeDef: ClassTypeDef) extends Pattern { // c: Class
    val subPatterns = Seq.empty
  }
  case class WildcardPattern(binder: Option[Identifier]) extends Pattern { // c @ _
    val subPatterns = Seq.empty
  } 
  case class CaseClassPattern(binder: Option[Identifier], caseClassDef: CaseClassDef, subPatterns: Seq[Pattern]) extends Pattern
  // case class ExtractorPattern(binder: Option[Identifier], 
  //   		      extractor : ExtractorTypeDef, 
  //   		      subPatterns: Seq[Pattern]) extends Pattern // c @ Extractor(...,...)
  // We don't handle Seq stars for now.

  /* Propositional logic */
  object And {
    def apply(l: Expr, r: Expr) : Expr = (l,r) match {
      case (BooleanLiteral(true),_) => r
      case (_,BooleanLiteral(true)) => l
      case _ => new And(Seq(l,r))
    }
    def apply(exprs: Seq[Expr]) : Expr = {
      val simpler = exprs.filter(_ != BooleanLiteral(true))
      if(simpler.isEmpty) BooleanLiteral(true) else simpler.reduceRight(And(_,_))
    }

    def unapply(and: And) : Option[Seq[Expr]] = 
      if(and == null) None else Some(and.exprs)
  }

  class And(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  object Or {
    def apply(l: Expr, r: Expr) : Expr = (l,r) match {
      case (BooleanLiteral(false),_) => r
      case (_,BooleanLiteral(false)) => l
      case _ => new Or(Seq(l,r))
    }
    def apply(exprs: Seq[Expr]) : Expr = {
      val simpler = exprs.filter(_ != BooleanLiteral(false))
      if(simpler.isEmpty) BooleanLiteral(false) else simpler.reduceRight(Or(_,_))
    }

    def unapply(or: Or) : Option[Seq[Expr]] = 
      if(or == null) None else Some(or.exprs)
  }

  class Or(val exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
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
    // if(left.getType != BooleanType || right.getType != BooleanType) {
    //   println("culprits: " + left.getType + ", " + right.getType)
    //   assert(false)
    // }
  }

  case class Not(expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
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
  }
  
  case class Variable(id: Identifier) extends Expr with Terminal {
    override def getType = id.getType
    override def setType(tt: TypeTree) = { id.setType(tt); this }
  }

  case class DeBruijnIndex(index: Int) extends Expr with Terminal

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
  case object UnitLiteral extends Literal[Unit] with FixedType {
    val fixedType = UnitType
    val value = ()
  }

  case class CaseClass(classDef: CaseClassDef, args: Seq[Expr]) extends Expr with FixedType {
    val fixedType = CaseClassType(classDef)
  }
  case class CaseClassInstanceOf(classDef: CaseClassDef, expr: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
  case class CaseClassSelector(classDef: CaseClassDef, caseClass: Expr, selector: Identifier) extends Expr with FixedType {
    val fixedType = classDef.fields.find(_.id == selector).get.getType
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

  /* Option expressions */
  case class OptionSome(value: Expr) extends Expr 
  case class OptionNone(baseType: TypeTree) extends Expr with Terminal with FixedType {
    val fixedType = OptionType(baseType)
  }

  /* Set expressions */
  case class EmptySet(baseType: TypeTree) extends Expr with Terminal
  case class FiniteSet(elements: Seq[Expr]) extends Expr 
  case class ElementOfSet(element: Expr, set: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
  case class SetCardinality(set: Expr) extends Expr with FixedType {
    val fixedType = Int32Type
  }
  case class SubsetOf(set1: Expr, set2: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }
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
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* List operations */
  case class NilList(baseType: TypeTree) extends Expr with Terminal
  case class Cons(head: Expr, tail: Expr) extends Expr 
  case class Car(list: Expr) extends Expr 
  case class Cdr(list: Expr) extends Expr 
  case class Concat(list1: Expr, list2: Expr) extends Expr 
  case class ListAt(list: Expr, index: Expr) extends Expr 

  /* Function operations */
  case class AnonymousFunction(entries: Seq[(Seq[Expr],Expr)], elseValue: Expr) extends Expr
  case class AnonymousFunctionInvocation(id: Identifier, args: Seq[Expr]) extends Expr

  /* Constraint programming */
  case class Distinct(exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  object UnaryOperator {
    def unapply(expr: Expr) : Option[(Expr,(Expr)=>Expr)] = expr match {
      case Not(t) => Some((t,Not(_)))
      case UMinus(t) => Some((t,UMinus))
      case SetCardinality(t) => Some((t,SetCardinality))
      case MultisetCardinality(t) => Some((t,MultisetCardinality))
      case MultisetToSet(t) => Some((t,MultisetToSet))
      case Car(t) => Some((t,Car))
      case Cdr(t) => Some((t,Cdr))
      case SetMin(s) => Some((s,SetMin))
      case SetMax(s) => Some((s,SetMax))
      case CaseClassSelector(cd, e, sel) => Some((e, CaseClassSelector(cd, _, sel)))
      case CaseClassInstanceOf(cd, e) => Some((e, CaseClassInstanceOf(cd, _)))
      case Assignment(id, e) => Some((e, Assignment(id, _)))
      case TupleSelect(t, i) => Some((t, TupleSelect(_, i)))
      case _ => None
    }
  }

  object BinaryOperator {
    def unapply(expr: Expr) : Option[(Expr,Expr,(Expr,Expr)=>Expr)] = expr match {
      case Equals(t1,t2) => Some((t1,t2,Equals.apply))
      case Iff(t1,t2) => Some((t1,t2,Iff(_,_)))
      case Implies(t1,t2) => Some((t1,t2,Implies.apply))
      case Plus(t1,t2) => Some((t1,t2,Plus))
      case Minus(t1,t2) => Some((t1,t2,Minus))
      case Times(t1,t2) => Some((t1,t2,Times))
      case Division(t1,t2) => Some((t1,t2,Division))
      case Modulo(t1,t2) => Some((t1,t2,Modulo))
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
      case MapIsDefinedAt(t1,t2) => Some((t1,t2, MapIsDefinedAt))
      case Concat(t1,t2) => Some((t1,t2,Concat))
      case ListAt(t1,t2) => Some((t1,t2,ListAt))
      case wh@While(t1, t2) => Some((t1,t2, (t1, t2) => While(t1, t2).setInvariant(wh.invariant).setPosInfo(wh)))
      case _ => None
    }
  }

  object NAryOperator {
    def unapply(expr: Expr) : Option[(Seq[Expr],(Seq[Expr])=>Expr)] = expr match {
      case fi @ FunctionInvocation(fd, args) => Some((args, (as => FunctionInvocation(fd, as).setPosInfo(fi))))
      case AnonymousFunctionInvocation(id, args) => Some((args, (as => AnonymousFunctionInvocation(id, as))))
      case CaseClass(cd, args) => Some((args, CaseClass(cd, _)))
      case And(args) => Some((args, And.apply))
      case Or(args) => Some((args, Or.apply))
      case FiniteSet(args) => Some((args, FiniteSet))
      case FiniteMap(args) => Some((args, (as : Seq[Expr]) => FiniteMap(as.asInstanceOf[Seq[SingletonMap]])))
      case FiniteMultiset(args) => Some((args, FiniteMultiset))
      case Distinct(args) => Some((args, Distinct))
      case Block(args, rest) => Some((args :+ rest, exprs => Block(exprs.init, exprs.last)))
      case Tuple(args) => Some((args, Tuple))
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
    searchAndReplaceDFS(substs.get)(expr)
  }

  // Can't just be overloading because of type erasure :'(
  def replaceFromIDs(substs: Map[Identifier,Expr], expr: Expr) : Expr = {
    replace(substs.map(p => (Variable(p._1) -> p._2)), expr)
  }

  def searchAndReplace(subst: Expr=>Option[Expr], recursive: Boolean=true)(expr: Expr) : Expr = {
    def rec(ex: Expr, skip: Expr = null) : Expr = (if (ex == skip) None else subst(ex)) match {
      case Some(newExpr) => {
        if(newExpr.getType == Untyped) {
          Settings.reporter.error("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
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
        case l @ LetVar(i,e,b) => {
          val re = rec(e)
          val rb = rec(b)
          if(re != e || rb != b)
            LetVar(i, re, rb).setType(l.getType)
          else
            l
        }
        case l @ LetDef(fd, b) => {
          //TODO, not sure, see comment for the next LetDef
          fd.body = fd.body.map(rec(_))
          fd.precondition = fd.precondition.map(rec(_))
          fd.postcondition = fd.postcondition.map(rec(_))
          LetDef(fd, rec(b)).setType(l.getType)
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
        case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType).setPosInfo(m)
        case t if t.isInstanceOf[Terminal] => t
        case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
      }
    }

    def inCase(cse: MatchCase) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  def searchAndReplaceDFS(subst: Expr=>Option[Expr])(expr: Expr) : Expr = {
    val (res,_) = searchAndReplaceDFSandTrackChanges(subst)(expr)
    res
  }

  def searchAndReplaceDFSandTrackChanges(subst: Expr=>Option[Expr])(expr: Expr) : (Expr,Boolean) = {
    var somethingChanged: Boolean = false
    def applySubst(ex: Expr) : Expr = subst(ex) match {
      case None => ex
      case Some(newEx) => {
        somethingChanged = true
        if(newEx.getType == Untyped) {
          Settings.reporter.warning("REPLACING WITH AN UNTYPED EXPRESSION !")
          Settings.reporter.warning("Here's the new expression: " + newEx)
        }
        newEx
      }
    }

    def rec(ex: Expr) : Expr = ex match {
      case l @ Let(i,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        applySubst(if(re != e || rb != b) {
          Let(i,re,rb).setType(l.getType)
        } else {
          l
        })
      }
      case l @ LetVar(i,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        applySubst(if(re != e || rb != b) {
          LetVar(i,re,rb).setType(l.getType)
        } else {
          l
        })
      }
      case l @ LetDef(fd,b) => {
        //TODO: Not sure: I actually need the replace to occurs even in the pre/post condition, hope this is correct
        fd.body = fd.body.map(rec(_))
        fd.precondition = fd.precondition.map(rec(_))
        fd.postcondition = fd.postcondition.map(rec(_))
        val rl = LetDef(fd, rec(b)).setType(l.getType)
        applySubst(rl)
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
        applySubst(if(change) {
          recons(rargs).setType(n.getType)
        } else {
          n
        })
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        applySubst(if(r1 != t1 || r2 != t2) {
          recons(r1,r2).setType(b.getType)
        } else {
          b
        })
      }
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t)
        applySubst(if(r != t) {
          recons(r).setType(u.getType)
        } else {
          u
        })
      }
      case i @ IfExpr(t1,t2,t3) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        val r3 = rec(t3)
        applySubst(if(r1 != t1 || r2 != t2 || r3 != t3) {
          IfExpr(r1,r2,r3).setType(i.getType)
        } else {
          i
        })
      }
      case m @ MatchExpr(scrut,cses) => {
        val rscrut = rec(scrut)
        val (newCses,changes) = cses.map(inCase(_)).unzip
        applySubst(if(rscrut != scrut || changes.exists(res=>res)) {
          MatchExpr(rscrut, newCses).setType(m.getType).setPosInfo(m)
        } else {
          m
        })
      }
      case t if t.isInstanceOf[Terminal] => applySubst(t)
      case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplaceDFS: " + unhandled)
    }

    def inCase(cse: MatchCase) : (MatchCase,Boolean) = cse match {
      case s @ SimpleCase(pat, rhs) => {
        val rrhs = rec(rhs)
        if(rrhs != rhs) {
          (SimpleCase(pat, rrhs), true)
        } else {
          (s, false)
        }
      }
      case g @ GuardedCase(pat, guard, rhs) => {
        val rguard = rec(guard)
        val rrhs = rec(rhs)
        if(rguard != guard || rrhs != rhs) {
          (GuardedCase(pat, rguard, rrhs), true)
        } else {
          (g, false)
        }
      }
    }

    val res = rec(expr)
    (res, somethingChanged)
  }

  // rewrites pattern-matching expressions to use fresh variables for the binders
  def freshenLocals(expr: Expr) : Expr = {
    def rewritePattern(p: Pattern, sm: Map[Identifier,Identifier]) : Pattern = p match {
      case InstanceOfPattern(Some(b), ctd) => InstanceOfPattern(Some(sm(b)), ctd)
      case WildcardPattern(Some(b)) => WildcardPattern(Some(sm(b)))
      case CaseClassPattern(ob, ccd, sps) => CaseClassPattern(ob.map(sm(_)), ccd, sps.map(rewritePattern(_, sm)))
      case other => other
    }

    def freshenCase(cse: MatchCase) : MatchCase = {
      val allBinders: Set[Identifier] = cse.pattern.binders
      val subMap: Map[Identifier,Identifier] = Map(allBinders.map(i => (i, FreshIdentifier(i.name, true).setType(i.getType))).toSeq : _*)
      val subVarMap: Map[Expr,Expr] = subMap.map(kv => (Variable(kv._1) -> Variable(kv._2)))
      
      cse match {
        case SimpleCase(pattern, rhs) => SimpleCase(rewritePattern(pattern, subMap), replace(subVarMap, rhs))
        case GuardedCase(pattern, guard, rhs) => GuardedCase(rewritePattern(pattern, subMap), replace(subVarMap, guard), replace(subVarMap, rhs))
      }
    }

    def applyToTree(e : Expr) : Option[Expr] = e match {
      case m @ MatchExpr(s, cses) => Some(MatchExpr(s, cses.map(freshenCase(_))).setType(m.getType).setPosInfo(m))
      case l @ Let(i,e,b) => {
        val newID = FreshIdentifier(i.name, true).setType(i.getType)
        Some(Let(newID, e, replace(Map(Variable(i) -> Variable(newID)), b)))
      }
      case _ => None
    }

    searchAndReplaceDFS(applyToTree)(expr)
  }

  // convert describes how to compute a value for the leaves (that includes
  // functions with no args.)
  // combine descriess how to combine two values
  def treeCatamorphism[A](convert: Expr=>A, combine: (A,A)=>A, expression: Expr) : A = {
    treeCatamorphism(convert, combine, (e:Expr,a:A)=>a, expression)
  }
  // compute allows the catamorphism to change the combined value depending on the tree
  def treeCatamorphism[A](convert: Expr=>A, combine: (A,A)=>A, compute: (Expr,A)=>A, expression: Expr) : A = {
    def rec(expr: Expr) : A = expr match {
      case l @ Let(_, e, b) => compute(l, combine(rec(e), rec(b)))
      case l @ LetVar(_, e, b) => compute(l, combine(rec(e), rec(b)))
      case l @ LetDef(fd, b) => compute(l, combine(rec(fd.getBody), rec(b))) //TODO, still not sure about the semantic
      case n @ NAryOperator(args, _) => {
        if(args.size == 0)
          compute(n, convert(n))
        else
          compute(n, args.map(rec(_)).reduceLeft(combine))
      }
      case b @ BinaryOperator(a1,a2,_) => compute(b, combine(rec(a1),rec(a2)))
      case u @ UnaryOperator(a,_) => compute(u, rec(a))
      case i @ IfExpr(a1,a2,a3) => compute(i, combine(combine(rec(a1), rec(a2)), rec(a3)))
      case m @ MatchExpr(scrut, cses) => compute(m, (scrut +: cses.flatMap(_.expressions)).map(rec(_)).reduceLeft(combine))
      case a @ AnonymousFunction(es, ev) => compute(a, (es.flatMap(e => e._1 ++ Seq(e._2)) ++ Seq(ev)).map(rec(_)).reduceLeft(combine))
      case t: Terminal => compute(t, convert(t))
      case unhandled => scala.sys.error("Non-terminal case should be handled in treeCatamorphism: " + unhandled)
    }

    rec(expression)
  }

  def flattenBlocks(expr: Expr): Expr = {
    def applyToTree(expr: Expr): Option[Expr] = expr match {
      case Block(exprs, last) => {
        val nexprs = (exprs :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
          case UnitLiteral => Seq()
          case e2 => Seq(e2)
        }
        val fexpr = nexprs match {
          case Seq() => UnitLiteral
          case Seq(e) => e
          case es => Block(es.init, es.last).setType(es.last.getType)
        }
        Some(fexpr)
      }
      case _ => None
    }
    searchAndReplaceDFS(applyToTree)(expr)
  }

  //checking whether the expr is pure, that is do not contains any non-pure construct: assign, while and blocks
  def isPure(expr: Expr): Boolean = {
    def convert(t: Expr) : Boolean = t match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case _ => true
    }
    def combine(b1: Boolean, b2: Boolean) = b1 && b2
    def compute(e: Expr, b: Boolean) = e match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case _ => true
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def variablesOf(expr: Expr) : Set[Identifier] = {
    def convert(t: Expr) : Set[Identifier] = t match {
      case Variable(i) => Set(i)
      case _ => Set.empty
    }
    def combine(s1: Set[Identifier], s2: Set[Identifier]) = s1 ++ s2
    def compute(t: Expr, s: Set[Identifier]) = t match {
      case Let(i,_,_) => s -- Set(i)
      case MatchExpr(_, cses) => s -- (cses.map(_.pattern.binders).foldLeft(Set[Identifier]())((a, b) => a ++ b))
      case AnonymousFunctionInvocation(i,_) => s ++ Set[Identifier](i)
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def containsFunctionCalls(expr : Expr) : Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case f : FunctionInvocation => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case f : FunctionInvocation => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def topLevelFunctionCallsOf(expr: Expr, barring : Set[FunDef] = Set.empty) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(fd, _) if(!barring(fd)) => Set(f)
      case _ => Set.empty
    }
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2
    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(fd,  _) if(!barring(fd)) => Set(f) // ++ s that's the difference with the one below
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def allNonRecursiveFunctionCallsOf(expr: Expr, program: Program) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(fd, _) if program.isRecursive(fd) => Set(f)
      case _ => Set.empty
    }
    
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2

    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(fd,_) if program.isRecursive(fd) => Set(f) ++ s
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def functionCallsOf(expr: Expr) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(_, _) => Set(f)
      case _ => Set.empty
    }
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2
    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(_, _) => Set(f) ++ s
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def contains(expr: Expr, matcher: Expr=>Boolean) : Boolean = {
    treeCatamorphism[Boolean](
      matcher,
      (b1: Boolean, b2: Boolean) => b1 || b2,
      (t: Expr, b: Boolean) => b || matcher(t),
      expr)
  }

  def allIdentifiers(expr: Expr) : Set[Identifier] = expr match {
    case l @ Let(binder, e, b) => allIdentifiers(e) ++ allIdentifiers(b) + binder
    case l @ LetVar(binder, e, b) => allIdentifiers(e) ++ allIdentifiers(b) + binder
    case l @ LetDef(fd, b) => allIdentifiers(fd.getBody) ++ allIdentifiers(b) + fd.id
    case n @ NAryOperator(args, _) =>
      (args map (Trees.allIdentifiers(_))).foldLeft(Set[Identifier]())((a, b) => a ++ b)
    case b @ BinaryOperator(a1,a2,_) => allIdentifiers(a1) ++ allIdentifiers(a2)
    case u @ UnaryOperator(a,_) => allIdentifiers(a)
    case i @ IfExpr(a1,a2,a3) => allIdentifiers(a1) ++ allIdentifiers(a2) ++ allIdentifiers(a3)
    case m @ MatchExpr(scrut, cses) =>
      (cses map (_.allIdentifiers)).foldLeft(Set[Identifier]())((a, b) => a ++ b) ++ allIdentifiers(scrut)
    case Variable(id) => Set(id)
    case t: Terminal => Set.empty
  }

  def allDeBruijnIndices(expr: Expr) : Set[DeBruijnIndex] =  {
    def convert(t: Expr) : Set[DeBruijnIndex] = t match {
      case i @ DeBruijnIndex(idx) => Set(i)
      case _ => Set.empty
    }
    def combine(s1: Set[DeBruijnIndex], s2: Set[DeBruijnIndex]) = s1 ++ s2
    treeCatamorphism(convert, combine, expr)
  }

  /* Simplifies let expressions:
   *  - removes lets when expression never occurs
   *  - simplifies when expressions occurs exactly once
   *  - expands when expression is just a variable.
   * Note that the code is simple but far from optimal (many traversals...)
   */
  def simplifyLets(expr: Expr) : Expr = {
    def simplerLet(t: Expr) : Option[Expr] = t match {
      case letExpr @ Let(i, t: Terminal, b) => Some(replace(Map((Variable(i) -> t)), b))
      case letExpr @ Let(i,e,b) => {
        val occurences = treeCatamorphism[Int]((e:Expr) => e match {
          case Variable(x) if x == i => 1
          case _ => 0
        }, (x:Int,y:Int)=>x+y, b)
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

  // Pulls out all let constructs to the top level, and makes sure they're
  // properly ordered.
  private type DefPair  = (Identifier,Expr) 
  private type DefPairs = List[DefPair] 
  private def allLetDefinitions(expr: Expr) : DefPairs = treeCatamorphism[DefPairs](
    (e: Expr) => Nil,
    (s1: DefPairs, s2: DefPairs) => s1 ::: s2,
    (e: Expr, dps: DefPairs) => e match {
      case Let(i, e, _) => (i,e) :: dps
      case _ => dps
    },
    expr)
  
  private def killAllLets(expr: Expr) : Expr = searchAndReplaceDFS((e: Expr) => e match {
    case Let(_,_,ex) => Some(ex)
    case _ => None
  })(expr)

  def liftLets(expr: Expr) : Expr = {
    val initialDefinitionPairs = allLetDefinitions(expr)
    val definitionPairs = initialDefinitionPairs.map(p => (p._1, killAllLets(p._2)))
    val occursLists : Map[Identifier,Set[Identifier]] = Map(definitionPairs.map((dp: DefPair) => (dp._1 -> variablesOf(dp._2).toSet.filter(_.isLetBinder))) : _*)
    var newList : DefPairs = Nil
    var placed  : Set[Identifier] = Set.empty
    val toPlace = definitionPairs.size
    var placedC = 0
    var traversals = 0

    while(placedC < toPlace) {
      if(traversals > toPlace + 1) {
        scala.sys.error("Cycle in let definitions or multiple definition for the same identifier in liftLets : " + definitionPairs.mkString("\n"))
      }
      for((id,ex) <- definitionPairs) if (!placed(id)) {
        if((occursLists(id) -- placed) == Set.empty) {
          placed = placed + id
          newList = (id,ex) :: newList
          placedC = placedC + 1
        }
      }
      traversals = traversals + 1
    }

    val noLets = killAllLets(expr)

    val res = (newList.foldLeft(noLets)((e,iap) => Let(iap._1, iap._2, e)))
    simplifyLets(res)
  }

  def wellOrderedLets(tree : Expr) : Boolean = {
    val pairs = allLetDefinitions(tree)
    val definitions: Set[Identifier] = Set(pairs.map(_._1) : _*)
    val vars: Set[Identifier] = variablesOf(tree)
    val intersection = vars intersect definitions
    if(!intersection.isEmpty) {
      intersection.foreach(id => {
        Settings.reporter.error("Variable with identifier '" + id + "' has escaped its let-definition !")
      })
      false
    } else {
      vars.forall(id => if(id.isLetBinder) {
        Settings.reporter.error("Variable with identifier '" + id + "' has lost its let-definition (it disappeared??)")
        false
      } else {
        true
      })
    }
  }

  /* Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut, s), cses.map(inCase(_, s))).setType(m.getType).setPosInfo(m)
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
      case unhandled => scala.sys.error("Unhandled case in expandLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs, s))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard, s), rec(rhs, s))
    }

    rec(expr, Map.empty)
  }

  object SimplePatternMatching {
    def isSimple(me: MatchExpr) : Boolean = unapply(me).isDefined

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

  private var matchConverterCache = new scala.collection.mutable.HashMap[Expr,Expr]()
  /** Rewrites all pattern-matching expressions into if-then-else expressions,
   * with additional error conditions. Does not introduce additional variables.
   * We use a cache because we can. */
  def matchToIfThenElse(expr: Expr) : Expr = {
    val toRet = if(matchConverterCache.isDefinedAt(expr)) {
      matchConverterCache(expr)
    } else {
      val converted = convertMatchToIfThenElse(expr)
      matchConverterCache(expr) = converted
      converted
    }

    toRet
  }

  private def convertMatchToIfThenElse(expr: Expr) : Expr = {
    def mapForPattern(in: Expr, pattern: Pattern) : Map[Identifier,Expr] = pattern match {
      case WildcardPattern(None) => Map.empty
      case WildcardPattern(Some(id)) => Map(id -> in)
      case InstanceOfPattern(None, _) => Map.empty
      case InstanceOfPattern(Some(id), _) => Map(id -> in)
      case CaseClassPattern(b, ccd, subps) => {
        assert(ccd.fields.size == subps.size)
        val pairs = ccd.fields.map(_.id).toList zip subps.toList
        val subMaps = pairs.map(p => mapForPattern(CaseClassSelector(ccd, in, p._1), p._2))
        val together = subMaps.foldLeft(Map.empty[Identifier,Expr])(_ ++ _)
        b match {
          case Some(id) => Map(id -> in) ++ together
          case None => together
        }
      }
    }

    def conditionForPattern(in: Expr, pattern: Pattern) : Expr = pattern match {
      case WildcardPattern(_) => BooleanLiteral(true)
      case InstanceOfPattern(_,_) => scala.sys.error("InstanceOfPattern not yet supported.")
      case CaseClassPattern(_, ccd, subps) => {
        assert(ccd.fields.size == subps.size)
        val pairs = ccd.fields.map(_.id).toList zip subps.toList
        val subTests = pairs.map(p => conditionForPattern(CaseClassSelector(ccd, in, p._1), p._2))
        val together = And(subTests)
        And(CaseClassInstanceOf(ccd, in), together)
      }
    }

    def rewritePM(e: Expr) : Option[Expr] = e match {
      case m @ MatchExpr(scrut, cases) => {
        // println("Rewriting the following PM: " + e)

        val condsAndRhs = for(cse <- cases) yield {
          val map = mapForPattern(scrut, cse.pattern)
          val patCond = conditionForPattern(scrut, cse.pattern)
          val realCond = cse.theGuard match {
            case Some(g) => And(patCond, replaceFromIDs(map, g))
            case None => patCond
          }
          val newRhs = replaceFromIDs(map, cse.rhs)
          (realCond, newRhs)
        } 

        val optCondsAndRhs = if(SimplePatternMatching.isSimple(m)) {
          // this is a hackish optimization: because we know all cases are covered, we replace the last condition by true (and that drops the check)
          val lastExpr = condsAndRhs.last._2

          condsAndRhs.dropRight(1) ++ Seq((BooleanLiteral(true),lastExpr))
        } else {
          condsAndRhs
        }

        val bigIte = optCondsAndRhs.foldRight[Expr](Error("non-exhaustive match").setType(bestRealType(m.getType)).setPosInfo(m))((p1, ex) => {
          if(p1._1 == BooleanLiteral(true)) {
            p1._2
          } else {
            IfExpr(p1._1, p1._2, ex).setType(m.getType)
          }
        })

        Some(bigIte)
      }
      case _ => None
    }
    
    searchAndReplaceDFS(rewritePM)(expr)
  }

  private var mapGetConverterCache = new scala.collection.mutable.HashMap[Expr,Expr]()
  /** Rewrites all map accesses with additional error conditions. */
  def mapGetWithChecks(expr: Expr) : Expr = {
    val toRet = if (mapGetConverterCache.isDefinedAt(expr)) {
      mapGetConverterCache(expr)
    } else {
      val converted = convertMapGet(expr)
      mapGetConverterCache(expr) = converted
      converted
    }

    toRet
  }

  private def convertMapGet(expr: Expr) : Expr = {
    def rewriteMapGet(e: Expr) : Option[Expr] = e match {
      case mg @ MapGet(m,k) => 
        val ida = MapIsDefinedAt(m, k)
        Some(IfExpr(ida, mg, Error("key not found for map access").setType(mg.getType)).setType(mg.getType))
      case _ => None
    }

    searchAndReplaceDFS(rewriteMapGet)(expr)
  }

  // prec: expression does not contain match expressions
  def measureADTChildrenDepth(expression: Expr) : Int = {
    import scala.math.max

    def rec(ex: Expr, lm: Map[Identifier,Int]) : Int = ex match {
      case Let(i,e,b) => rec(b,lm + (i -> rec(e,lm)))
      case Variable(id) => lm.getOrElse(id, 0)
      case CaseClassSelector(_, e, _) => rec(e,lm) + 1
      case NAryOperator(args, _) => if(args.isEmpty) 0 else args.map(rec(_,lm)).max
      case BinaryOperator(e1,e2,_) => max(rec(e1,lm), rec(e2,lm))
      case UnaryOperator(e,_) => rec(e,lm)
      case IfExpr(c,t,e) => max(max(rec(c,lm),rec(t,lm)),rec(e,lm))
      case t: Terminal => 0
      case _ => scala.sys.error("Not handled in measureChildrenDepth : " + ex)
    }
    
    rec(expression,Map.empty)
  }

  private val random = new scala.util.Random()

  def randomValue(v: Variable) : Expr = randomValue(v.getType)
  def simplestValue(v: Variable) : Expr = simplestValue(v.getType)

  def randomValue(tpe: TypeTree) : Expr = tpe match {
    case Int32Type => IntLiteral(random.nextInt(42))
    case BooleanType => BooleanLiteral(random.nextBoolean())
    case AbstractClassType(acd) =>
      val children = acd.knownChildren
      randomValue(classDefToClassType(children(random.nextInt(children.size))))
    case CaseClassType(cd) =>
      val fields = cd.fields
      CaseClass(cd, fields.map(f => randomValue(f.getType)))
    case _ => throw new Exception("I can't choose random value for type " + tpe)
  }

  def simplestValue(tpe: TypeTree) : Expr = tpe match {
    case Int32Type => IntLiteral(0)
    case BooleanType => BooleanLiteral(false)
    case AbstractClassType(acd) => {
      val children = acd.knownChildren
      val simplerChildren = children.filter{
        case ccd @ CaseClassDef(id, Some(parent), fields) =>
          !fields.exists(vd => vd.getType match {
            case AbstractClassType(fieldAcd) => acd == fieldAcd
            case CaseClassType(fieldCcd) => ccd == fieldCcd
            case _ => false
          })
        case _ => false
      }
      def orderByNumberOfFields(fst: ClassTypeDef, snd: ClassTypeDef) : Boolean = (fst, snd) match {
        case (CaseClassDef(_, _, flds1), CaseClassDef(_, _, flds2)) => flds1.size <= flds2.size
        case _ => true
      }
      val orderedChildren = simplerChildren.sortWith(orderByNumberOfFields)
      simplestValue(classDefToClassType(orderedChildren.head))
    }
    case CaseClassType(ccd) =>
      val fields = ccd.fields
      CaseClass(ccd, fields.map(f => simplestValue(f.getType)))
    case SetType(baseType) => EmptySet(baseType).setType(tpe)
    case MapType(fromType, toType) => EmptyMap(fromType, toType).setType(tpe)
    case FunctionType(fromTypes, toType) => AnonymousFunction(Seq.empty, simplestValue(toType)).setType(tpe)
    case _ => throw new Exception("I can't choose simplest value for type " + tpe)
  }
}
