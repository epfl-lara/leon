package leon
package purescala

/** AST definitions for Pure Scala. */
object Trees {
  import Common._
  import TypeTrees._
  import Definitions._
  import Extractors._
  import TreeOps._

  /* EXPRESSIONS */

  abstract class Expr extends Typed with Serializable {
    override def toString: String = PrettyPrinter(this)
  }

  trait Terminal {
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

  case class Epsilon(pred: Expr) extends Expr with ScalacPositional

  case class Choose(vars: List[Identifier], pred: Expr) extends Expr with ScalacPositional

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

  case class LetTuple(binders: Seq[Identifier], value: Expr, body: Expr) extends Expr {
    binders.foreach(_.markAsLetBinder)
    val et = body.getType
    if(et != Untyped)
      setType(et)
  }

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

  case class Tuple(exprs: Seq[Expr]) extends Expr {
    val subTpes = exprs.map(_.getType).map(bestRealType)
    if(!subTpes.exists(_ == Untyped)) {
      setType(TupleType(subTpes))
    }

  }

  // This must be 1-indexed !
  case class TupleSelect(tuple: Expr, index: Int) extends Expr {
    assert(index >= 1)
  }

  case class Waypoint(i: Int, expr: Expr) extends Expr

  object MatchExpr {
    def apply(scrutinee: Expr, cases: Seq[MatchCase]) : MatchExpr = {
      scrutinee.getType match {
        case a: AbstractClassType => new MatchExpr(scrutinee, cases)
        case c: CaseClassType => new MatchExpr(scrutinee, cases.filter(_.pattern match {
          case CaseClassPattern(_, ccd, _) if ccd != c.classDef => false
          case _ => true
        }))
        case t: TupleType => new MatchExpr(scrutinee, cases)
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
      TreeOps.allIdentifiers(rhs) ++ 
      theGuard.map(TreeOps.allIdentifiers(_)).getOrElse(Set[Identifier]()) ++ 
      (expressions map (TreeOps.allIdentifiers(_))).foldLeft(Set[Identifier]())((a, b) => a ++ b)
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

  case class TuplePattern(binder: Option[Identifier], subPatterns: Seq[Pattern]) extends Pattern


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

  object TopLevelAnds { // expr1 AND (expr2 AND (expr3 AND ..)) => List(expr1, expr2, expr3)
    def unapply(e: Expr): Option[Seq[Expr]] = e match {
      case And(exprs) =>
        Some(exprs.flatMap(unapply(_).flatten))
      case e =>
        Some(Seq(e))
    }
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

  case class EpsilonVariable(pos: (Int, Int)) extends Expr with Terminal

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

  case class MapGet(map: Expr, key: Expr) extends Expr with ScalacPositional
  case class MapUnion(map1: Expr, map2: Expr) extends Expr 
  case class MapDifference(map: Expr, keys: Expr) extends Expr 
  case class MapIsDefinedAt(map: Expr, key: Expr) extends Expr with FixedType {
    val fixedType = BooleanType
  }

  /* Array operations */
  case class ArrayFill(length: Expr, defaultValue: Expr) extends Expr
  case class ArrayMake(defaultValue: Expr) extends Expr
  case class ArraySelect(array: Expr, index: Expr) extends Expr with ScalacPositional
  //the difference between ArrayUpdate and ArrayUpdated is that the former has a side effect while the latter is the function variant
  //ArrayUpdate should be eliminated soon in the analysis while ArrayUpdated is keep all the way to the backend
  case class ArrayUpdate(array: Expr, index: Expr, newValue: Expr) extends Expr with ScalacPositional with FixedType {
    val fixedType = UnitType
  }
  case class ArrayUpdated(array: Expr, index: Expr, newValue: Expr) extends Expr with ScalacPositional
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

  /* Function operations */
  case class AnonymousFunction(entries: Seq[(Seq[Expr],Expr)], elseValue: Expr) extends Expr
  case class AnonymousFunctionInvocation(id: Identifier, args: Seq[Expr]) extends Expr

  /* Constraint programming */
  case class Distinct(exprs: Seq[Expr]) extends Expr with FixedType {
    val fixedType = BooleanType
  }


  object SimplePatternMatching {
    def isSimple(me: MatchExpr) : Boolean = unapply(me).isDefined

    // (scrutinee, classtype, list((caseclassdef, variable, list(variable), rhs)))
    def unapply(e: MatchExpr) : Option[(Expr,ClassType,Seq[(CaseClassDef,Identifier,Seq[Identifier],Expr)])] = {
      val MatchExpr(scrutinee, cases) = e
      val sType = scrutinee.getType

      if(sType.isInstanceOf[TupleType]) {
        None
      } else if(sType.isInstanceOf[AbstractClassType]) {
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
    case TuplePattern(_, subps) => {
      val TupleType(tpes) = in.getType
      assert(tpes.size == subps.size)
      val subTests = subps.zipWithIndex.map{case (p, i) => conditionForPattern(TupleSelect(in, i+1).setType(tpes(i)), p)}
      And(subTests)
    }
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
      case TuplePattern(b, subps) => {
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map{case (p, i) => mapForPattern(TupleSelect(in, i+1).setType(tpes(i)), p)}
        val map = maps.foldLeft(Map.empty[Identifier,Expr])(_ ++ _)
        b match {
          case Some(id) => map + (id -> in)
          case None => map
        }
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
        Some(IfExpr(ida, mg, Error("key not found for map access").setType(mg.getType).setPosInfo(mg)).setType(mg.getType))
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

  //guarentee that all IfExpr will be at the top level and as soon as you encounter a non-IfExpr, then no more IfExpr can be find in the sub-expressions
  //require no-match, no-ets and only pure code
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(IfExpr(c, t, e), op) => Some(IfExpr(c, op(t).setType(uop.getType), op(e).setType(uop.getType)).setType(uop.getType))
      case bop@BinaryOperator(IfExpr(c, t, e), t2, op) => Some(IfExpr(c, op(t, t2).setType(bop.getType), op(e, t2).setType(bop.getType)).setType(bop.getType))
      case bop@BinaryOperator(t1, IfExpr(c, t, e), op) => Some(IfExpr(c, op(t1, t).setType(bop.getType), op(t1, e).setType(bop.getType)).setType(bop.getType))
      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).setType(nop.getType),
            op(beforeIte ++ Seq(e) ++ afterIte).setType(nop.getType)
          ).setType(nop.getType))
        }
      }
      case _ => None
    }

    def fix[A](f: (A) => A, a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f, na)
    }
    fix(searchAndReplaceDFS(transform), expr)
  }

}
