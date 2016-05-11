/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Types._
import Definitions._
import Expressions._
import Extractors._
import Constructors._
import utils._
import solvers._
import scala.language.implicitConversions

/** Provides functions to manipulate [[purescala.Expressions]].
  *
  * This object provides a few generic operations on Leon expressions,
  * as well as some common operations.
  *
  * The generic operations lets you apply operations on a whole tree
  * expression. You can look at:
  *   - [[GenTreeOps.fold foldRight]]
  *   - [[GenTreeOps.preTraversal preTraversal]]
  *   - [[GenTreeOps.postTraversal postTraversal]]
  *   - [[GenTreeOps.preMap preMap]]
  *   - [[GenTreeOps.postMap postMap]]
  *   - [[GenTreeOps.genericTransform genericTransform]]
  *
  * These operations usually take a higher order function that gets applied to the
  * expression tree in some strategy. They provide an expressive way to build complex
  * operations on Leon expressions.
  *
  */
object ExprOps extends GenTreeOps[Expr] {

  val Deconstructor = Operator

  /** Replaces bottom-up sub-identifiers by looking up for them in a map */
  def replaceFromIDs(substs: Map[Identifier, Expr], expr: Expr) : Expr = {
    postMap({
      case Variable(i) => substs.get(i)
      case _ => None
    })(expr)
  }

  def preTransformWithBinders(f: (Expr, Set[Identifier]) => Expr, initBinders: Set[Identifier] = Set())(e: Expr) = {
    import xlang.Expressions.LetVar
    def rec(binders: Set[Identifier], e: Expr): Expr = f(e, binders) match {
      case ld@LetDef(fds, bd) =>
        fds.foreach(fd => {
          fd.fullBody = rec(binders ++ fd.paramIds, fd.fullBody)
        })
        LetDef(fds, rec(binders, bd)).copiedFrom(ld)
      case l@Let(i, v, b) =>
        Let(i, rec(binders + i, v), rec(binders + i, b)).copiedFrom(l)
      case lv@LetVar(i, v, b) =>
        LetVar(i, rec(binders + i, v), rec(binders + i, b)).copiedFrom(lv)
      case m@MatchExpr(scrut, cses) =>
        MatchExpr(rec(binders, scrut), cses map { case mc@MatchCase(pat, og, rhs) =>
          val newBs = binders ++ pat.binders
          MatchCase(pat, og map (rec(newBs, _)), rec(newBs, rhs)).copiedFrom(mc)
        }).copiedFrom(m)
      case p@Passes(in, out, cses) =>
        Passes(rec(binders, in), rec(binders, out), cses map { case mc@MatchCase(pat, og, rhs) =>
          val newBs = binders ++ pat.binders
          MatchCase(pat, og map (rec(newBs, _)), rec(newBs, rhs)).copiedFrom(mc)
        }).copiedFrom(p)
      case l@Lambda(args, bd) =>
        Lambda(args, rec(binders ++ args.map(_.id), bd)).copiedFrom(l)
      case f@Forall(args, bd) =>
        Forall(args, rec(binders ++ args.map(_.id), bd)).copiedFrom(f)
      case d@Deconstructor(subs, builder) =>
        builder(subs map (rec(binders, _))).copiedFrom(d)
    }

    rec(initBinders, e)
  }

  /** Returns the set of free variables in an expression */
  def variablesOf(expr: Expr): Set[Identifier] = {
    import leon.xlang.Expressions._
    fold[Set[Identifier]] {
      case (e, subs) =>
        val subvs = subs.flatten.toSet
        e match {
          case Variable(i) => subvs + i
          case Old(i) => subvs + i
          case LetDef(fds, _) => subvs -- fds.flatMap(_.params.map(_.id))
          case Let(i, _, _) => subvs - i
          case LetVar(i, _, _) => subvs - i
          case MatchExpr(_, cses) => subvs -- cses.flatMap(_.pattern.binders)
          case Passes(_, _, cses) => subvs -- cses.flatMap(_.pattern.binders)
          case Lambda(args, _) => subvs -- args.map(_.id)
          case Forall(args, _) => subvs -- args.map(_.id)
          case _ => subvs
        }
    }(expr)
  }

  /** Returns true if the expression contains a function call */
  def containsFunctionCalls(expr: Expr): Boolean = {
    exists{
      case _: FunctionInvocation => true
      case _ => false
    }(expr)
  }

  /** Returns all Function calls found in the expression */
  def functionCallsOf(expr: Expr): Set[FunctionInvocation] = {
    collect[FunctionInvocation] {
      case f: FunctionInvocation => Set(f)
      case _ => Set()
    }(expr)
  }
  
  def nestedFunDefsOf(expr: Expr): Set[FunDef] = {
    collect[FunDef] {
      case LetDef(fds, _) => fds.toSet
      case _ => Set()
    }(expr)
  }

  /** Returns functions in directly nested LetDefs */
  def directlyNestedFunDefs(e: Expr): Set[FunDef] = {
    fold[Set[FunDef]]{
      case (LetDef(fds,_), fromFdsFromBd) => fromFdsFromBd.last ++ fds
      case (_,             subs) => subs.flatten.toSet
    }(e)
  }

  /** Computes the negation of a boolean formula, with some simplifications. */
  def negate(expr: Expr) : Expr = {
    //require(expr.getType == BooleanType)
    (expr match {
      case Let(i,b,e) => Let(i,b,negate(e))
      case Not(e) => e
      case Implies(e1,e2) => and(e1, negate(e2))
      case Or(exs) => and(exs map negate: _*)
      case And(exs) => or(exs map negate: _*)
      case LessThan(e1,e2) => GreaterEquals(e1,e2)
      case LessEquals(e1,e2) => GreaterThan(e1,e2)
      case GreaterThan(e1,e2) => LessEquals(e1,e2)
      case GreaterEquals(e1,e2) => LessThan(e1,e2)
      case IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2))
      case BooleanLiteral(b) => BooleanLiteral(!b)
      case e => Not(e)
    }).setPos(expr)
  }

  def replacePatternBinders(pat: Pattern, subst: Map[Identifier, Identifier]): Pattern = {
    def rec(p: Pattern): Pattern = p match {
      case InstanceOfPattern(ob, ctd) => InstanceOfPattern(ob map subst, ctd)
      case WildcardPattern(ob) => WildcardPattern(ob map subst)
      case TuplePattern(ob, sps) => TuplePattern(ob map subst, sps map rec)
      case CaseClassPattern(ob, ccd, sps) => CaseClassPattern(ob map subst, ccd, sps map rec)
      case UnapplyPattern(ob, obj, sps) => UnapplyPattern(ob map subst, obj, sps map rec)
      case LiteralPattern(ob, lit) => LiteralPattern(ob map subst, lit)
    }

    rec(pat)
  }


  /** Replace each node by its constructor
    *
    * Remap the expression by calling the corresponding constructor
    * for each node of the expression. The constructor will perfom
    * some local simplifications, resulting in a simplified expression.
    */
  def simplifyByConstructors(expr: Expr): Expr = {
    def step(e: Expr): Option[Expr] = e match {
      case Not(t) => Some(not(t))
      case UMinus(t) => Some(uminus(t))
      case BVUMinus(t) => Some(uminus(t))
      case RealUMinus(t) => Some(uminus(t))
      case CaseClassSelector(cd, e, sel) => Some(caseClassSelector(cd, e, sel))
      case AsInstanceOf(e, ct) => Some(asInstOf(e, ct))
      case Equals(t1, t2) => Some(equality(t1, t2))
      case Implies(t1, t2) => Some(implies(t1, t2))
      case Plus(t1, t2) => Some(plus(t1, t2))
      case Minus(t1, t2) => Some(minus(t1, t2))
      case Times(t1, t2) => Some(times(t1, t2))
      case BVPlus(t1, t2) => Some(plus(t1, t2))
      case BVMinus(t1, t2) => Some(minus(t1, t2))
      case BVTimes(t1, t2) => Some(times(t1, t2))
      case RealPlus(t1, t2) => Some(plus(t1, t2))
      case RealMinus(t1, t2) => Some(minus(t1, t2))
      case RealTimes(t1, t2) => Some(times(t1, t2))
      case And(args) => Some(andJoin(args))
      case Or(args) => Some(orJoin(args))
      case Tuple(args) => Some(tupleWrap(args))
      case MatchExpr(scrut, cases) => Some(matchExpr(scrut, cases))
      case Passes(in, out, cases) => Some(passes(in, out, cases))
      case _ => None
    }
    postMap(step)(expr)
  }

  /** ATTENTION: Unused, and untested
    * rewrites pattern-matching expressions to use fresh variables for the binders
    */
  def freshenLocals(expr: Expr) : Expr = {
    def freshenCase(cse: MatchCase) : MatchCase = {
      val allBinders: Set[Identifier] = cse.pattern.binders
      val subMap: Map[Identifier,Identifier] =
        Map(allBinders.map(i => (i, FreshIdentifier(i.name, i.getType, true))).toSeq : _*)
      val subVarMap: Map[Expr,Expr] = subMap.map(kv => Variable(kv._1) -> Variable(kv._2))

      MatchCase(
        replacePatternBinders(cse.pattern, subMap),
        cse.optGuard map { replace(subVarMap, _)},
        replace(subVarMap,cse.rhs)
      )
    }

    postMap{
      case m @ MatchExpr(s, cses) =>
        Some(matchExpr(s, cses.map(freshenCase)).copiedFrom(m))

      case p @ Passes(in, out, cses) =>
        Some(Passes(in, out, cses.map(freshenCase)).copiedFrom(p))

      case l @ Let(i,e,b) =>
        val newID = FreshIdentifier(i.name, i.getType, alwaysShowUniqueID = true).copiedFrom(i)
        Some(Let(newID, e, replaceFromIDs(Map(i -> Variable(newID)), b)).copiedFrom(l))

      case _ => None
    }(expr)
  }

  /** Applies the function to the I/O constraint and simplifies the resulting constraint */
  def applyAsMatches(p : Passes, f : Expr => Expr) = {
    f(p.asConstraint) match {
      case Equals(newOut, MatchExpr(newIn, newCases)) =>
        val filtered = newCases flatMap {
          case MatchCase(p, g, `newOut`) => None
          case other => Some(other)
        }
        Passes(newIn, newOut, filtered)
      case other =>
        other
    }
  }

  /** Normalizes the expression expr */
  def normalizeExpression(expr: Expr) : Expr = {
    def rec(e: Expr): Option[Expr] = e match {
      case TupleSelect(Let(id, v, b), ts) =>
        Some(Let(id, v, tupleSelect(b, ts, true)))

      case TupleSelect(LetTuple(ids, v, b), ts) =>
        Some(letTuple(ids, v, tupleSelect(b, ts, true)))

      case CaseClassSelector(cct, cc: CaseClass, id) =>
        Some(caseClassSelector(cct, cc, id).copiedFrom(e))

      case IfExpr(c, thenn, elze) if (thenn == elze) && isPurelyFunctional(c) =>
        Some(thenn)

      case IfExpr(c, BooleanLiteral(true), BooleanLiteral(false)) =>
        Some(c)

      case IfExpr(Not(c), thenn, elze) =>
        Some(IfExpr(c, elze, thenn).copiedFrom(e))

      case IfExpr(c, BooleanLiteral(false), BooleanLiteral(true)) =>
        Some(Not(c).copiedFrom(e))

      case FunctionInvocation(tfd, List(IfExpr(c, thenn, elze))) =>
        Some(IfExpr(c, FunctionInvocation(tfd, List(thenn)), FunctionInvocation(tfd, List(elze))).copiedFrom(e))

      case _ =>
        None
    }

    fixpoint(postMap(rec))(expr)
  }

  private val typedIds: scala.collection.mutable.Map[TypeTree, List[Identifier]] =
    scala.collection.mutable.Map.empty.withDefaultValue(List.empty)

  /** Normalizes identifiers in an expression to enable some notion of structural
    * equality between expressions on which usual equality doesn't make sense
    * (i.e. closures).
    *
    * This function relies on the static map `typedIds` to ensure identical
    * structures and must therefore be synchronized.
    *
    * The optional argument [[onlySimple]] determines whether non-simple expressions
    * (see [[isSimple]]) should be normalized into a dependency or recursed into
    * (when they don't depend on [[args]]). This distinction is used in the
    * unrolling solver to provide geenral equality checks between functions even when
    * they have complex closures.
    */
  def normalizeStructure(args: Seq[Identifier], expr: Expr, onlySimple: Boolean = true): (Seq[Identifier], Expr, Map[Identifier, Expr]) = synchronized {
    val vars = args.toSet

    class Normalizer extends TreeTransformer {
      var subst: Map[Identifier, Expr] = Map.empty
      var remainingIds: Map[TypeTree, List[Identifier]] = typedIds.toMap

      def getId(e: Expr): Identifier = {
        val tpe = TypeOps.bestRealType(e.getType)
        val newId = remainingIds.get(tpe) match {
          case Some(x :: xs) =>
            remainingIds += tpe -> xs
            x
          case _ =>
            val x = FreshIdentifier("x", tpe, true)
            typedIds(tpe) = typedIds(tpe) :+ x
            x
        }
        subst += newId -> e
        newId
      }

      override def transform(id: Identifier): Identifier = subst.get(id) match {
        case Some(Variable(newId)) => newId
        case Some(_) => scala.sys.error("Should never happen!")
        case None => getId(id.toVariable)
      }

      override def transform(e: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = e match {
        case expr if (isSimple(expr) || !onlySimple) && (variablesOf(expr) & vars).isEmpty => getId(expr).toVariable
        case f: Forall =>
          val (args, body, newSubst) = normalizeStructure(f.args.map(_.id), f.body, onlySimple)
          subst ++= newSubst
          Forall(args.map(ValDef(_)), body)
        case l: Lambda =>
          val (args, body, newSubst) = normalizeStructure(l.args.map(_.id), l.body, onlySimple)
          subst ++= newSubst
          Lambda(args.map(ValDef(_)), body)
        case _ => super.transform(e)
      }
    }

    val n = new Normalizer
    val bindings = args.map(id => id -> n.getId(id.toVariable)).toMap
    val normalized = n.transform(matchToIfThenElse(expr))(bindings)

    val argsImgSet = bindings.map(_._2).toSet
    val bodySubst = n.subst.filter(p => !argsImgSet(p._1))

    (args.map(bindings), normalized, bodySubst)
  }

  def normalizeStructure(lambda: Lambda): (Lambda, Map[Identifier, Expr]) = {
    val (args, body, subst) = normalizeStructure(lambda.args.map(_.id), lambda.body, onlySimple = false)
    (Lambda(args.map(ValDef(_)), body), subst)
  }

  def normalizeStructure(forall: Forall): (Forall, Map[Identifier, Expr]) = {
    val (args, body, subst) = normalizeStructure(forall.args.map(_.id), forall.body)
    (Forall(args.map(ValDef(_)), body), subst)
  }

  /** Returns '''true''' if the formula is Ground,
    * which means that it does not contain any variable ([[purescala.ExprOps#variablesOf]] e is empty)
    * and [[purescala.ExprOps#isDeterministic isDeterministic]]
    */
  def isGround(e: Expr): Boolean = {
    variablesOf(e).isEmpty && isDeterministic(e)
  }

  /** Returns '''true''' if the formula is simple,
    * which means that it requires no special encoding for an
    * unrolling solver. See implementation for what this means exactly.
    */
  def isSimple(e: Expr): Boolean = !exists {
    case (_: Choose) | (_: Hole) |
         (_: Assert) | (_: Ensuring) |
         (_: Forall) | (_: Lambda) | (_: FiniteLambda) |
         (_: FunctionInvocation) | (_: Application) => true
    case _ => false
  } (e)

  /** Returns a function which can simplify all ground expressions which appear in a program context.
    */
  def evalGround(ctx: LeonContext, program: Program): Expr => Expr = {
    import evaluators._

    val eval = new DefaultEvaluator(ctx, program)

    def rec(e: Expr): Option[Expr] = e match {
      case l: Terminal => None
      case e if isGround(e) => eval.eval(e).result // returns None if eval fails
      case _ => None
    }

    preMap(rec)
  }

  /** Simplifies let expressions
    *
    *  - removes lets when expression never occurs
    *  - simplifies when expressions occurs exactly once
    *  - expands when expression is just a variable.
    *
    * @note the code is simple but far from optimal (many traversals...)
    */
  def simplifyLets(expr: Expr) : Expr = {

    def freeComputable(e: Expr) = e match {
      case TupleSelect(Variable(_), _) => true
      case CaseClassSelector(_, Variable(_), _) => true
      case FiniteSet(els, _) => els.isEmpty
      case FiniteMap(els, _, _) => els.isEmpty
      case _: Terminal => true
      case _ => false
    }

    def simplerLet(t: Expr): Option[Expr] = t match {

      /* Untangle */
      case Let(i1, Let(i2, e2, b2), b1) =>
        Some(Let(i2, e2, Let(i1, b2, b1)))

      case Let(i1, LetTuple(is2, e2, b2), b1) =>
        Some(letTuple(is2, e2, Let(i1, b2, b1)))

      case LetTuple(ids1, Let(id2, e2, b2), b1) =>
        Some(Let(id2, e2, letTuple(ids1, b2, b1)))

      case LetTuple(ids1, LetTuple(ids2, e2, b2), b1) =>
        Some(letTuple(ids2, e2, letTuple(ids1, b2, b1)))

      // Untuple
      case Let(id, Tuple(es), b) =>
        val ids = es.zipWithIndex.map { case (e, ind) =>
          FreshIdentifier(id + (ind + 1).toString, e.getType, true)
        }
        val theMap: Map[Expr, Expr] = es.zip(ids).zipWithIndex.map {
          case ((e, subId), ind) => TupleSelect(Variable(id), ind + 1) -> Variable(subId)
        }.toMap

        val replaced0 = replace(theMap, b)
        val replaced  = replace(Map(Variable(id) -> Tuple(ids map Variable)), replaced0)

        Some(letTuple(ids, Tuple(es), replaced))

      case Let(i, e, b) if freeComputable(e) && isPurelyFunctional(e) =>
        // computation is very quick and code easy to read, always inline
        Some(replaceFromIDs(Map(i -> e), b))

      case Let(i,e,b) if isPurelyFunctional(e) =>
        // computation may be slow, or code complicated to read, inline at most once
        val occurrences = count {
          case Variable(`i`) => 1
          case _ => 0
        }(b)

        if(occurrences == 0) {
          Some(b)
        } else if(occurrences == 1) {
          Some(replaceFromIDs(Map(i -> e), b))
        } else {
          None
        }

      case LetTuple(ids, Tuple(elems), body) =>
        Some(ids.zip(elems).foldRight(body) { case ((id, elem), bd) => Let(id, elem, bd) })

      /*case LetPattern(patt, e0, body) if isPurelyFunctional(e0) =>
        // Will turn the match-expression with a single case into a list of lets.
        // @mk it is not clear at all that we want this

        // Just extra safety...
        val e = (e0.getType, patt) match {
          case (_:AbstractClassType, CaseClassPattern(_, cct, _)) =>
            asInstOf(e0, cct)
          case (at: AbstractClassType, InstanceOfPattern(_, ct)) if at != ct =>
            asInstOf(e0, ct)
          case _ =>
            e0
        }

        // Sort lets in dependency order
        val lets = mapForPattern(e, patt).toSeq.sortWith {
          case ((id1, e1), (id2, e2)) => exists{ _ == Variable(id1) }(e2)
        }

        Some(lets.foldRight(body) {
          case ((id, e), bd) => Let(id, e, bd)
        })*/

      case MatchExpr(scrut, cases) =>
        // Merge match within match
        var changed = false
        val newCases = cases map {
          case MatchCase(patt, g, LetPattern(innerPatt, Variable(id), body)) if patt.binders contains id =>
            changed = true
            val newPatt = PatternOps.preMap {
              case WildcardPattern(Some(`id`)) => Some(innerPatt.withBinder(id))
              case _ => None
            }(patt)
            MatchCase(newPatt, g, body)
          case other =>
            other
        }
        if(changed) Some(MatchExpr(scrut, newCases)) else None

      case _ => None
    }

    postMap(simplerLet, applyRec = true)(expr)
  }

  /** Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s))
      case m @ MatchExpr(scrut, cses) => matchExpr(rec(scrut, s), cses.map(inCase(_, s))).setPos(m)
      case p @ Passes(in, out, cses) => Passes(rec(in, s), rec(out,s), cses.map(inCase(_, s))).setPos(p)
      case n @ Deconstructor(args, recons) =>
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
          recons(rargs)
        else
          n
      case unhandled => throw LeonFatalError("Unhandled case in expandLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = {
      import cse._
      MatchCase(pattern, optGuard map { rec(_, s) }, rec(rhs,s))
    }

    rec(expr, Map.empty)
  }

  /** Lifts lets to top level.
    *
    * Does not push any used variable out of scope.
    * Assumes no match expressions (i.e. matchToIfThenElse has been called on e)
    */
  def liftLets(e: Expr): Expr = {

    type C = Seq[(Identifier, Expr)]

    def combiner(e: Expr, defs: Seq[C]): C = (e, defs) match {
      case (Let(i, ex, b), Seq(inDef, inBody)) =>
        inDef ++ ((i, ex) +: inBody)
      case _ =>
        defs.flatten
    }

    def noLet(e: Expr, defs: C) = e match {
      case Let(_, _, b) => (b, defs)
      case _ => (e, defs)
    }

    val (bd, defs) = genericTransform[C](noTransformer, noLet, combiner)(Seq())(e)

    defs.foldRight(bd){ case ((id, e), body) => Let(id, e, body) }
  }

  /** Generates substitutions necessary to transform scrutinee to equivalent
    * specialized cases
    *
    * {{{
    *    e match {
    *     case CaseClass((a, 42), c) => expr
    *    }
    * }}}
    * will return, for the first pattern:
    * {{{
    *    Map(
    *     e -> CaseClass(t, c),
    *     t -> (a, b2),
    *     b2 -> 42,
    *    )
    * }}}
    *
    * @note UNUSED, is not maintained
    */
  def patternSubstitutions(in: Expr, pattern: Pattern): Seq[(Expr, Expr)] ={
    def rec(in: Expr, pattern: Pattern): Seq[(Expr, Expr)] = pattern match {
      case InstanceOfPattern(ob, cct: CaseClassType) =>
        val pt = CaseClassPattern(ob, cct, cct.fields.map { f =>
          WildcardPattern(Some(FreshIdentifier(f.id.name, f.getType)))
        })
        rec(in, pt)

      case TuplePattern(_, subps) =>
        val TupleType(subts) = in.getType
        val subExprs = (subps zip subts).zipWithIndex map {
          case ((p, t), index) => p.binder.map(_.toVariable).getOrElse(tupleSelect(in, index+1, subps.size))
        }

        // Special case to get rid of (a,b) match { case (c,d) => .. }
        val subst0 = in match {
          case Tuple(ts) =>
            ts zip subExprs
          case _ =>
            Seq(in -> tupleWrap(subExprs))
        }

        subst0 ++ ((subExprs zip subps) flatMap {
          case (e, p) => recBinder(e, p)
        })

      case CaseClassPattern(_, cct, subps) =>
        val subExprs = (subps zip cct.classDef.fields) map {
          case (p, f) => p.binder.map(_.toVariable).getOrElse(caseClassSelector(cct, in, f.id))
        }

        // Special case to get rid of Cons(a,b) match { case Cons(c,d) => .. }
        val subst0 = in match {
          case CaseClass(`cct`, args) =>
            args zip subExprs
          case _ =>
            Seq(in -> CaseClass(cct, subExprs))
        }

        subst0 ++ ((subExprs zip subps) flatMap {
          case (e, p) => recBinder(e, p)
        })

      case LiteralPattern(_, v) =>
        Seq(in -> v)

      case _ =>
        Seq()
    }

    def recBinder(in: Expr, pattern: Pattern): Seq[(Expr, Expr)] = {
      (pattern, pattern.binder) match {
        case (_: WildcardPattern, Some(b)) =>
          Seq(in -> b.toVariable)
        case (p, Some(b)) =>
          val bv = b.toVariable
          Seq(in -> bv) ++ rec(bv, pattern)
        case _ =>
          rec(in, pattern)
      }
    }

    recBinder(in, pattern).filter{ case (a, b) => a != b }
  }

  /** Recursively transforms a pattern on a boolean formula expressing the conditions for the input expression, possibly including name binders
    *
    * For example, the following pattern on the input `i`
    * {{{
    * case m @ MyCaseClass(t: B, (_, 7)) =>
    * }}}
    * will yield the following condition before simplification (to give some flavour)
    *
    * {{{and(IsInstanceOf(MyCaseClass, i), and(Equals(m, i), InstanceOfClass(B, i.t), equals(i.k.arity, 2), equals(i.k._2, 7))) }}}
    *
    * Pretty-printed, this would be:
    * {{{
    * i.instanceOf[MyCaseClass] && m == i && i.t.instanceOf[B] && i.k.instanceOf[Tuple2] && i.k._2 == 7
    * }}}
    *
    * @see [[purescala.Expressions.Pattern]]
    */
  def conditionForPattern(in: Expr, pattern: Pattern, includeBinders: Boolean = false): Path = {
    def bind(ob: Option[Identifier], to: Expr): Path = {
      if (!includeBinders) {
        Path.empty
      } else {
        ob.map(id => Path.empty withBinding (id -> to)).getOrElse(Path.empty)
      }
    }

    def rec(in: Expr, pattern: Pattern): Path = {
      pattern match {
        case WildcardPattern(ob) =>
          bind(ob, in)

        case InstanceOfPattern(ob, ct) =>
          if (ct.parent.isEmpty) {
            bind(ob, in)
          } else {
            Path(IsInstanceOf(in, ct)) merge bind(ob, in)
          }

        case CaseClassPattern(ob, cct, subps) =>
          assert(cct.classDef.fields.size == subps.size)
          val pairs = cct.classDef.fields.map(_.id).toList zip subps.toList
          val subTests = pairs.map(p => rec(caseClassSelector(cct, in, p._1), p._2))
          val together = subTests.foldLeft(bind(ob, in))(_ merge _)
          Path(IsInstanceOf(in, cct)) merge together

        case TuplePattern(ob, subps) =>
          val TupleType(tpes) = in.getType
          assert(tpes.size == subps.size)
          val subTests = subps.zipWithIndex.map{case (p, i) => rec(tupleSelect(in, i+1, subps.size), p)}
          subTests.foldLeft(bind(ob, in))(_ merge _)

        case up @ UnapplyPattern(ob, fd, subps) =>
          def someCase(e: Expr) = {
            // In the case where unapply returns a Some, it is enough that the subpatterns match
            val subTests = unwrapTuple(e, subps.size) zip subps map { case (ex, p) => rec(ex, p) }
            subTests.foldLeft(Path.empty)(_ merge _).toClause
          }
          Path(up.patternMatch(in, BooleanLiteral(false), someCase).setPos(in)) merge bind(ob, in)

        case LiteralPattern(ob, lit) =>
          Path(Equals(in, lit)) merge bind(ob, in)
      }
    }

    rec(in, pattern)
  }

  /** Converts the pattern applied to an input to a map between identifiers and expressions */
  def mapForPattern(in: Expr, pattern: Pattern) : Map[Identifier,Expr] = {
    def bindIn(id: Option[Identifier], cast: Option[ClassType] = None): Map[Identifier,Expr] = id match {
      case None => Map()
      case Some(id) => Map(id -> cast.map(asInstOf(in, _)).getOrElse(in))
    }
    pattern match {
      case CaseClassPattern(b, cct, subps) =>
        assert(cct.fields.size == subps.size)
        val pairs = cct.classDef.fields.map(_.id).toList zip subps.toList
        val subMaps = pairs.map(p => mapForPattern(caseClassSelector(cct, asInstOf(in, cct), p._1), p._2))
        val together = subMaps.flatten.toMap
        bindIn(b, Some(cct)) ++ together

      case TuplePattern(b, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map{case (p, i) => mapForPattern(tupleSelect(in, i+1, subps.size), p)}
        val map = maps.flatten.toMap
        bindIn(b) ++ map

      case up@UnapplyPattern(b, _, subps) =>
        bindIn(b) ++ unwrapTuple(up.getUnsafe(in), subps.size).zip(subps).flatMap {
          case (e, p) => mapForPattern(e, p)
        }.toMap

      case InstanceOfPattern(b, ct) =>
        bindIn(b, Some(ct))

      case other =>
        bindIn(other.binder)
    }
  }

  /** Rewrites all pattern-matching expressions into if-then-else expressions
    * Introduces additional error conditions. Does not introduce additional variables.
    */
  def matchToIfThenElse(expr: Expr): Expr = {

    def rewritePM(e: Expr): Option[Expr] = e match {
      case m @ MatchExpr(scrut, cases) =>
        // println("Rewriting the following PM: " + e)

        val condsAndRhs = for (cse <- cases) yield {
          val map = mapForPattern(scrut, cse.pattern)
          val patCond = conditionForPattern(scrut, cse.pattern, includeBinders = false)
          val realCond = cse.optGuard match {
            case Some(g) => patCond withCond replaceFromIDs(map, g)
            case None => patCond
          }
          val newRhs = replaceFromIDs(map, cse.rhs)
          (realCond.toClause, newRhs, cse)
        }

        val bigIte = condsAndRhs.foldRight[Expr](Error(m.getType, "Match is non-exhaustive").copiedFrom(m))((p1, ex) => {
          if(p1._1 == BooleanLiteral(true)) {
            p1._2
          } else {
            IfExpr(p1._1, p1._2, ex).copiedFrom(p1._3)
          }
        })

        Some(bigIte)

      case p: Passes =>
        // This introduces a MatchExpr
        Some(p.asConstraint)

      case _ => None
    }

    preMap(rewritePM)(expr)
  }

  /** For each case in the [[purescala.Expressions.MatchExpr MatchExpr]], concatenates the path condition with the newly induced conditions.
   *
   *  Each case holds the conditions on other previous cases as negative.
   *
    * @see [[purescala.ExprOps#conditionForPattern conditionForPattern]]
    * @see [[purescala.ExprOps#mapForPattern mapForPattern]]
    */
  def matchExprCaseConditions(m: MatchExpr, path: Path) : Seq[Path] = {
    val MatchExpr(scrut, cases) = m
    var pcSoFar = path

    for (c <- cases) yield {
      val g = c.optGuard getOrElse BooleanLiteral(true)
      val cond = conditionForPattern(scrut, c.pattern, includeBinders = true)
      val localCond = pcSoFar merge (cond withCond g)

      // These contain no binders defined in this MatchCase
      val condSafe = conditionForPattern(scrut, c.pattern)
      val gSafe = replaceFromIDs(mapForPattern(scrut, c.pattern), g)
      pcSoFar = pcSoFar merge (condSafe withCond gSafe).negate

      localCond
    }
  }

  /** Condition to pass this match case, expressed w.r.t scrut only */
  def matchCaseCondition(scrut: Expr, c: MatchCase): Path = {

    val patternC = conditionForPattern(scrut, c.pattern, includeBinders = false)

    c.optGuard match {
      case Some(g) =>
        // guard might refer to binders
        val map  = mapForPattern(scrut, c.pattern)
        patternC withCond replaceFromIDs(map, g)

      case None =>
        patternC
    }
  }

  /** Returns the path conditions for each of the case passes.
    *
    * Each case holds the conditions on other previous cases as negative.
    */
  def passesPathConditions(p: Passes, pathCond: Path) : Seq[Path] = {
    matchExprCaseConditions(MatchExpr(p.in, p.cases), pathCond)
  }

  /**
   * Returns a pattern from an expression, and a guard if any.
   */
  def expressionToPattern(e : Expr) : (Pattern, Expr) = {
    var guard : Expr = BooleanLiteral(true)
    def rec(e : Expr) : Pattern = e match {
      case CaseClass(cct, fields) => CaseClassPattern(None, cct, fields map rec)
      case Tuple(subs) => TuplePattern(None, subs map rec)
      case l : Literal[_] => LiteralPattern(None, l)
      case Variable(i) => WildcardPattern(Some(i))
      case other =>
        val id = FreshIdentifier("other", other.getType, true)
        guard = and(guard, Equals(Variable(id), other))
        WildcardPattern(Some(id))
    }
    (rec(e), guard)
  }

  /**
    * Takes a pattern and returns an expression that corresponds to it.
    * Also returns a sequence of `Identifier -> Expr` pairs which
    * represent the bindings for intermediate binders (from outermost to innermost)
    */
  def patternToExpression(p: Pattern, expectedType: TypeTree): (Expr, Seq[(Identifier, Expr)]) = {
    def fresh(tp : TypeTree) = FreshIdentifier("binder", tp, true)
    var ieMap = Seq[(Identifier, Expr)]()
    def addBinding(b : Option[Identifier], e : Expr) = b foreach { ieMap +:= (_, e) }
    def rec(p : Pattern, expectedType : TypeTree) : Expr = p match {
      case WildcardPattern(b) =>
        Variable(b getOrElse fresh(expectedType))
      case LiteralPattern(b, lit) =>
        addBinding(b,lit)
        lit
      case InstanceOfPattern(b, ct) => ct match {
        case act: AbstractClassType =>
          // @mk: This seems dubious, in the sense that it just binds the expression
          //      of the AbstractClassType to an id instead of going case-wise.
          //      I think this is sufficient for the use of this function though:
          //      it is only used to generate examples so it is followed by a type-aware enumerator.
          val e = Variable(fresh(act))
          addBinding(b, e)
          e

        case cct: CaseClassType =>
          val fields = cct.fields map { f => Variable(fresh(f.getType)) }
          val e = CaseClass(cct, fields)
          addBinding(b, e)
          e
      }
      case TuplePattern(b, subs) =>
        val TupleType(subTypes) = expectedType
        val e = Tuple(subs zip subTypes map {
          case (sub, subType) => rec(sub, subType)
        })
        addBinding(b, e)
        e
      case CaseClassPattern(b, cct, subs) =>
        val e = CaseClass(cct, subs zip cct.fieldsTypes map { case (sub,tp) => rec(sub,tp) })
        addBinding(b, e)
        e
      case up@UnapplyPattern(b, fd, subs) =>
        // TODO: Support this
        NoTree(expectedType)
    }

    (rec(p, expectedType), ieMap)

  }


  /** Rewrites all map accesses with additional error conditions. */
  def mapGetWithChecks(expr: Expr): Expr = {
    postMap({
      case mg @ MapApply(m,k) =>
        val ida = MapIsDefinedAt(m, k)
        Some(IfExpr(ida, mg, Error(mg.getType, "Key not found for map access").copiedFrom(mg)).copiedFrom(mg))

      case _=>
        None
    })(expr)
  }

  /** Returns simplest value of a given type */
  def simplestValue(tpe: TypeTree) : Expr = tpe match {
    case StringType                 => StringLiteral("")
    case Int32Type                  => IntLiteral(0)
    case RealType               	  => FractionalLiteral(0, 1)
    case IntegerType                => InfiniteIntegerLiteral(0)
    case CharType                   => CharLiteral('a')
    case BooleanType                => BooleanLiteral(false)
    case UnitType                   => UnitLiteral()
    case SetType(baseType)          => FiniteSet(Set(), baseType)
    case BagType(baseType)          => FiniteBag(Map(), baseType)
    case MapType(fromType, toType)  => FiniteMap(Map(), fromType, toType)
    case TupleType(tpes)            => Tuple(tpes.map(simplestValue))
    case ArrayType(tpe)             => EmptyArray(tpe)

    case act @ AbstractClassType(acd, tpe) =>
      val ccDesc = act.knownCCDescendants

      def isRecursive(cct: CaseClassType): Boolean = {
        cct.fieldsTypes.exists{
          case AbstractClassType(fieldAcd, _) => acd.root == fieldAcd.root
          case CaseClassType(fieldCcd, _) => acd.root == fieldCcd.root
          case _ => false
        }
      }

      val nonRecChildren = ccDesc.filterNot(isRecursive).sortBy(_.fields.size)

      nonRecChildren.headOption match {
        case Some(cct) =>
          simplestValue(cct)

        case None =>
          throw LeonFatalError(act +" does not seem to be well-founded")
      }

    case cct: CaseClassType =>
      CaseClass(cct, cct.fieldsTypes.map(t => simplestValue(t)))

    case tp: TypeParameter =>
      GenericValue(tp, 0)

    case ft @ FunctionType(from, to) =>
      FiniteLambda(Seq.empty, simplestValue(to), ft)

    case _ => throw LeonFatalError("I can't choose simplest value for type " + tpe)
  }

  /* Checks if a given expression is 'real' and does not contain generic
   * values. */
  def isRealExpr(v: Expr): Boolean = {
    !exists {
      case gv: GenericValue => true
      case _ => false
    }(v)
  }

  def valuesOf(tp: TypeTree): Stream[Expr] = {
    import utils.StreamUtils._
    tp match {
      case BooleanType =>
        Stream(BooleanLiteral(false), BooleanLiteral(true))
      case Int32Type =>
        Stream.iterate(0) { prev =>
          if (prev > 0) -prev else -prev + 1
        } map IntLiteral
      case IntegerType =>
        Stream.iterate(BigInt(0)) { prev =>
          if (prev > 0) -prev else -prev + 1
        } map InfiniteIntegerLiteral
      case UnitType =>
        Stream(UnitLiteral())
      case tp: TypeParameter =>
        Stream.from(0) map (GenericValue(tp, _))
      case TupleType(stps) =>
        cartesianProduct(stps map (tp => valuesOf(tp))) map Tuple
      case SetType(base) =>
        def elems = valuesOf(base)
        elems.scanLeft(Stream(FiniteSet(Set(), base): Expr)){ (prev, curr) =>
          prev flatMap {
            case fs@FiniteSet(elems, tp) =>
              Stream(fs, FiniteSet(elems + curr, tp))
          }
        }.flatten // FIXME Need cp οr is this fine?
      case cct: CaseClassType =>
        cartesianProduct(cct.fieldsTypes map valuesOf) map (CaseClass(cct, _))
      case act: AbstractClassType =>
        interleave(act.knownCCDescendants.map(cct => valuesOf(cct)))
    }
  }


  /** Hoists all IfExpr at top level.
    *
    * Guarantees that all IfExpr will be at the top level and as soon as you
    * encounter a non-IfExpr, then no more IfExpr can be found in the
    * sub-expressions
    *
    * Assumes no match expressions
    */
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case IfExpr(c, t, e) => None

      case nop@Deconstructor(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).copiedFrom(nop),
            op(beforeIte ++ Seq(e) ++ afterIte).copiedFrom(nop)
          ))
        }
      }
      case _ => None
    }

    postMap(transform, applyRec = true)(expr)
  }

  def simplifyPaths(sf: SolverFactory[Solver], initPC: Path = Path.empty): Expr => Expr = {
    new SimplifierWithPaths(sf, initPC).transform
  }

  trait Traverser[T] {
    def traverse(e: Expr): T
  }

  object CollectorWithPaths {
    def apply[T](p: PartialFunction[Expr,T]): CollectorWithPaths[(T, Path)] = new CollectorWithPaths[(T, Path)] {
      def collect(e: Expr, path: Path): Option[(T, Path)] = if (!p.isDefinedAt(e)) None else {
        Some(p(e) -> path)
      }
    }
  }

  trait CollectorWithPaths[T] extends TransformerWithPC with Traverser[Seq[T]] {
    protected val initPath: Path = Path.empty

    private var results: Seq[T] = Nil

    def collect(e: Expr, path: Path): Option[T]

    def walk(e: Expr, path: Path): Option[Expr] = None

    override def rec(e: Expr, path: Path) = {
      collect(e, path).foreach { results :+= _ }
      walk(e, path) match {
        case Some(r) => r
        case _ => super.rec(e, path)
      }
    }

    def traverse(funDef: FunDef): Seq[T] = traverse(funDef.fullBody)

    def traverse(e: Expr): Seq[T] = traverse(e, initPath)

    def traverse(e: Expr, init: Expr): Seq[T] = traverse(e, Path(init))

    def traverse(e: Expr, init: Path): Seq[T] = {
      results = Nil
      rec(e, init)
      results
    }
  }

  def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Path)] = {
    CollectorWithPaths(f).traverse(expr)
  }

  override def formulaSize(e: Expr): Int = e match {
    case ml: MatchExpr =>
      super.formulaSize(e) + ml.cases.map(cs => PatternOps.formulaSize(cs.pattern)).sum
    case _ =>
      super.formulaSize(e)
  }

  /** Returns true if the expression is deterministic /
    * does not contain any [[purescala.Expressions.Choose Choose]]
    * or [[purescala.Expressions.Hole Hole]] or [[purescala.Expressions.WithOracle WithOracle]]
    */
  def isDeterministic(e: Expr): Boolean = {
    exists {
      case _ : Choose | _: Hole | _: WithOracle => false
      case _ => true
    }(e)
  }

  /** Returns if this expression behaves as a purely functional construct,
    * i.e. always returns the same value (for the same environment) and has no side-effects
    */
  def isPurelyFunctional(e: Expr): Boolean = {
    exists {
      case _ : Error | _ : Choose | _: Hole | _: WithOracle => false
      case _ => true
    }(e)
  }

  /** Returns the value for an identifier given a model. */
  def valuateWithModel(model: Model)(id: Identifier): Expr = {
    model.getOrElse(id, simplestValue(id.getType))
  }

  /** Substitute (free) variables in an expression with values form a model.
    *
    * Complete with simplest values in case of incomplete model.
    */
  def valuateWithModelIn(expr: Expr, vars: Set[Identifier], model: Model): Expr = {
    val valuator = valuateWithModel(model) _
    replace(vars.map(id => Variable(id) -> valuator(id)).toMap, expr)
  }
  
  /** Simple, local optimization on string */
  def simplifyString(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case StringConcat(StringLiteral(""), b) => b
      case StringConcat(b, StringLiteral("")) => b
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a + b)
      case StringLength(StringLiteral(a)) => IntLiteral(a.length)
      case StringBigLength(StringLiteral(a)) => InfiniteIntegerLiteral(a.length)
      case SubString(StringLiteral(a), IntLiteral(start), IntLiteral(end)) => StringLiteral(a.substring(start.toInt, end.toInt))
      case BigSubString(StringLiteral(a), InfiniteIntegerLiteral(start), InfiniteIntegerLiteral(end)) => StringLiteral(a.substring(start.toInt, end.toInt))
      case _ => expr
    }).copiedFrom(expr)
    simplify0(expr)
    fixpoint(simplePostTransform(simplify0))(expr)
  }

  /** Simple, local simplification on arithmetic
    *
    * You should not assume anything smarter than some constant folding and
    * simple cancellation. To avoid infinite cycle we only apply simplification
    * that reduce the size of the tree. The only guarantee from this function is
    * to not augment the size of the expression and to be sound.
    */
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case Plus(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
      case Plus(InfiniteIntegerLiteral(zero), e) if zero == BigInt(0) => e
      case Plus(e, InfiniteIntegerLiteral(zero)) if zero == BigInt(0) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, InfiniteIntegerLiteral(i1)), InfiniteIntegerLiteral(i2)) => Plus(e, InfiniteIntegerLiteral(i1+i2))
      case Plus(Plus(InfiniteIntegerLiteral(i1), e), InfiniteIntegerLiteral(i2)) => Plus(InfiniteIntegerLiteral(i1+i2), e)

      case Minus(e, InfiniteIntegerLiteral(zero)) if zero == BigInt(0) => e
      case Minus(InfiniteIntegerLiteral(zero), e) if zero == BigInt(0) => UMinus(e)
      case Minus(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(InfiniteIntegerLiteral(x)) => InfiniteIntegerLiteral(-x)
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      case Times(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 * i2)
      case Times(InfiniteIntegerLiteral(one), e) if one == BigInt(1) => e
      case Times(InfiniteIntegerLiteral(mone), e) if mone == BigInt(-1) => UMinus(e)
      case Times(e, InfiniteIntegerLiteral(one)) if one == BigInt(1) => e
      case Times(InfiniteIntegerLiteral(zero), _) if zero == BigInt(0) => InfiniteIntegerLiteral(0)
      case Times(_, InfiniteIntegerLiteral(zero)) if zero == BigInt(0) => InfiniteIntegerLiteral(0)
      case Times(InfiniteIntegerLiteral(i1), Times(InfiniteIntegerLiteral(i2), t)) => Times(InfiniteIntegerLiteral(i1*i2), t)
      case Times(InfiniteIntegerLiteral(i1), Times(t, InfiniteIntegerLiteral(i2))) => Times(InfiniteIntegerLiteral(i1*i2), t)
      case Times(InfiniteIntegerLiteral(i), UMinus(e)) => Times(InfiniteIntegerLiteral(-i), e)
      case Times(UMinus(e), InfiniteIntegerLiteral(i)) => Times(e, InfiniteIntegerLiteral(-i))
      case Times(InfiniteIntegerLiteral(i1), Division(e, InfiniteIntegerLiteral(i2))) if i2 != BigInt(0) && i1 % i2 == BigInt(0) => Times(InfiniteIntegerLiteral(i1/i2), e)

      case Division(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) if i2 != BigInt(0) => InfiniteIntegerLiteral(i1 / i2)
      case Division(e, InfiniteIntegerLiteral(one)) if one == BigInt(1) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => InfiniteIntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => InfiniteIntegerLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      case StringConcat(StringLiteral(""), a) => a
      case StringConcat(a, StringLiteral("")) => a
      case StringConcat(StringLiteral(a), StringLiteral(b)) => StringLiteral(a+b)
      case StringConcat(StringLiteral(a), StringConcat(StringLiteral(b), c)) => StringConcat(StringLiteral(a+b), c)
      case StringConcat(StringConcat(c, StringLiteral(a)), StringLiteral(b)) => StringConcat(c, StringLiteral(a+b))
      case StringConcat(a, StringConcat(b, c)) => StringConcat(StringConcat(a, b), c)
      //default
      case e => e
    }).copiedFrom(expr)

    fixpoint(simplePostTransform(simplify0))(expr)
  }

  /**
   * Some helper methods for FractionalLiterals
   */
  def normalizeFraction(fl: FractionalLiteral) = {
    val FractionalLiteral(num, denom) = fl
    val modNum = if (num < 0) -num else num
    val modDenom = if (denom < 0) -denom else denom
    val divisor = modNum.gcd(modDenom)
    val simpNum = num / divisor
    val simpDenom = denom / divisor
    if (simpDenom < 0)
      FractionalLiteral(-simpNum, -simpDenom)
    else
      FractionalLiteral(simpNum, simpDenom)
  }

  val realzero = FractionalLiteral(0, 1)
  def floor(fl: FractionalLiteral): FractionalLiteral = {
    val FractionalLiteral(n, d) = normalizeFraction(fl)
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (n == 0) realzero
    else if (n > 0) {
      //perform integer division
      FractionalLiteral(n / d, 1)
    } else {
      //here the number is negative
      if (n % d == 0)
        FractionalLiteral(n / d, 1)
      else {
        //perform integer division and subtract 1
        FractionalLiteral(n / d - 1, 1)
      }
    }
  }

  /** Checks whether a predicate is inductive on a certain identifier.
    *
    * isInductive(foo(a, b), a) where a: List will check whether
    *    foo(Nil, b) and
    *    foo(t, b) => foo(Cons(h,t), b)
    */
  def isInductiveOn(sf: SolverFactory[Solver])(path: Path, on: Identifier): Boolean = on match {
    case IsTyped(origId, AbstractClassType(cd, tps)) =>

      val toCheck = cd.knownDescendants.collect {
        case ccd: CaseClassDef =>
          val cct = CaseClassType(ccd, tps)

          val isType = IsInstanceOf(Variable(on), cct)

          val recSelectors = (cct.classDef.fields zip cct.fieldsTypes).collect { 
            case (vd, tpe) if tpe == on.getType => vd.id
          }

          if (recSelectors.isEmpty) {
            Seq()
          } else {
            val v = Variable(on)

            recSelectors.map { s =>
              and(path and isType, not(replace(Map(v -> caseClassSelector(cct, v, s)), path.toClause)))
            }
          }
      }.flatten

      val solver = SimpleSolverAPI(sf)

      toCheck.forall { cond =>
        solver.solveSAT(cond)._1 match {
          case Some(false) =>
            true
          case Some(true)  =>
            false
          case None =>
            // Should we be optimistic here?
            false
        }
      }
    case _ =>
      false
  }
  
  type Apriori = Map[Identifier, Identifier]
  
  /** Checks whether two expressions can be homomorphic and returns the corresponding mapping */
  def canBeHomomorphic(t1: Expr, t2: Expr): Option[Map[Identifier, Identifier]] = {
    val freeT1Variables = ExprOps.variablesOf(t1)
    val freeT2Variables = ExprOps.variablesOf(t2)
    
    def mergeContexts(
        a: Option[Apriori],
        b: Apriori => Option[Apriori]):
        Option[Apriori] = a.flatMap(b)

    implicit class AugmentedContext(c: Option[Apriori]) {
      def &&(other: Apriori => Option[Apriori]): Option[Apriori] = mergeContexts(c, other)
      def --(other: Seq[Identifier]) =
        c.map(_ -- other)
    }
    implicit class AugmentedBoolean(c: Boolean) {
      def &&(other:  => Option[Apriori]) = if(c) other else None
    }
    implicit class AugmentedFilter(c: Apriori => Option[Apriori]) {
      def &&(other: Apriori => Option[Apriori]):
        Apriori => Option[Apriori]
      = (m: Apriori) => c(m).flatMap(mp => other(mp))
    }
    implicit class AugmentedSeq[T](c: Seq[T]) {
      def mergeall(p: T => Apriori => Option[Apriori])(apriori: Apriori) =
        (Option(apriori) /: c) {
          case (s, c) => s.flatMap(apriori => p(c)(apriori))
        }
    }
    implicit def noneToContextTaker(c: None.type) = {
      (m: Apriori) => None
    }


    def idHomo(i1: Identifier, i2: Identifier)(apriori: Apriori): Option[Apriori] = {
      if(!(freeT1Variables(i1) || freeT2Variables(i2)) || i1 == i2 || apriori.get(i1) == Some(i2)) Some(Map(i1 -> i2)) else None
    }
    def idOptionHomo(i1: Option[Identifier], i2: Option[Identifier])(apriori: Apriori): Option[Apriori] = {
      (i1.size == i2.size) && (i1 zip i2).headOption.flatMap(i => idHomo(i._1, i._2)(apriori))
    }

    def fdHomo(fd1: FunDef, fd2: FunDef)(apriori: Apriori): Option[Apriori] = {
      if(fd1.params.size == fd2.params.size) {
         val newMap = Map((
           (fd1.id -> fd2.id) +:
           (fd1.paramIds zip fd2.paramIds)): _*)
         Option(newMap) && isHomo(fd1.fullBody, fd2.fullBody)
      } else None
    }

    def isHomo(t1: Expr, t2: Expr)(apriori: Apriori): Option[Apriori] = {
      def casesMatch(cs1 : Seq[MatchCase], cs2 : Seq[MatchCase])(apriori: Apriori) : Option[Apriori] = {
        def patternHomo(p1: Pattern, p2: Pattern)(apriori: Apriori): Option[Apriori] = (p1, p2) match {
          case (InstanceOfPattern(ob1, cd1), InstanceOfPattern(ob2, cd2)) =>
            cd1 == cd2 && idOptionHomo(ob1, ob2)(apriori)

          case (WildcardPattern(ob1), WildcardPattern(ob2)) =>
            idOptionHomo(ob1, ob2)(apriori)

          case (CaseClassPattern(ob1, ccd1, subs1), CaseClassPattern(ob2, ccd2, subs2)) =>
            val m = idOptionHomo(ob1, ob2)(apriori)

            (ccd1 == ccd2 && subs1.size == subs2.size) && m &&
              ((subs1 zip subs2) mergeall { case (p1, p2) => patternHomo(p1, p2) })

          case (UnapplyPattern(ob1, TypedFunDef(fd1, ts1), subs1), UnapplyPattern(ob2, TypedFunDef(fd2, ts2), subs2)) =>
            val m = idOptionHomo(ob1, ob2)(apriori)

            (subs1.size == subs2.size && ts1 == ts2) && m && fdHomo(fd1, fd2) && (
              (subs1 zip subs2) mergeall { case (p1, p2) => patternHomo(p1, p2) })

          case (TuplePattern(ob1, subs1), TuplePattern(ob2, subs2)) =>
            val m = idOptionHomo(ob1, ob2)(apriori)

            (ob1.size == ob2.size && subs1.size == subs2.size) && m && (
              (subs1 zip subs2) mergeall { case (p1, p2) => patternHomo(p1, p2) })

          case (LiteralPattern(ob1, lit1), LiteralPattern(ob2,lit2)) =>
            lit1 == lit2 && idOptionHomo(ob1, ob2)(apriori)

          case _ =>
            None
        }

        (cs1 zip cs2).mergeall {
          case (MatchCase(p1, g1, e1), MatchCase(p2, g2, e2)) =>
            val h = patternHomo(p1, p2) _
            val g: Apriori => Option[Apriori] = (g1, g2) match {
              case (Some(g1), Some(g2)) => isHomo(g1, g2)(_)
              case (None, None) => (m: Apriori) => Some(m)
              case _ => None
            }
            val e = isHomo(e1, e2) _

            h && g && e
        }(apriori)
      }

      val res: Option[Apriori] = (t1, t2) match {
        case (Variable(i1), Variable(i2)) =>
          idHomo(i1, i2)(apriori)

        case (Let(id1, v1, e1), Let(id2, v2, e2)) =>
          
          isHomo(v1, v2)(apriori + (id1 -> id2)) &&
          isHomo(e1, e2)
          
        case (Hole(_, _), Hole(_, _)) =>
          None

        case (LetDef(fds1, e1), LetDef(fds2, e2)) =>
          fds1.size == fds2.size &&
          {
            val zipped = fds1.zip(fds2)
            (zipped mergeall (fds => fdHomo(fds._1, fds._2)))(apriori) &&
            isHomo(e1, e2)
          }

        case (MatchExpr(s1, cs1), MatchExpr(s2, cs2)) =>
          cs1.size == cs2.size && casesMatch(cs1,cs2)(apriori) && isHomo(s1, s2)

        case (Passes(in1, out1, cs1), Passes(in2, out2, cs2)) =>
          (cs1.size == cs2.size && casesMatch(cs1,cs2)(apriori)) && isHomo(in1,in2) && isHomo(out1,out2)

        case (FunctionInvocation(tfd1, args1), FunctionInvocation(tfd2, args2)) =>
          (if(tfd1 == tfd2) Some(apriori) else (apriori.get(tfd1.fd.id) match {
            case None =>
              isHomo(tfd1.fd.fullBody, tfd2.fd.fullBody)(apriori + (tfd1.fd.id -> tfd2.fd.id))
            case Some(fdid2) =>
              if(fdid2 == tfd2.fd.id) Some(apriori) else None
          })) &&
          tfd1.tps.zip(tfd2.tps).mergeall{
            case (t1, t2) => if(t1 == t2)
              (m: Apriori) => Option(m)
              else (m: Apriori) => None} &&
          (args1 zip args2).mergeall{ case (a1, a2) => isHomo(a1, a2) }

        case (Lambda(defs, body), Lambda(defs2, body2)) =>
          // We remove variables introduced by lambdas.
          ((defs zip defs2).mergeall{ case (ValDef(a1), ValDef(a2)) =>
            (m: Apriori) =>
              Some(m + (a1 -> a2)) }(apriori)
           && isHomo(body, body2)
          ) -- (defs.map(_.id))
          
        case (v1, v2) if isValue(v1) && isValue(v2) =>
          v1 == v2 && Some(apriori)

        case Same(Operator(es1, _), Operator(es2, _)) =>
          (es1.size == es2.size) &&
          (es1 zip es2).mergeall{ case (e1, e2) => isHomo(e1, e2) }(apriori)

        case _ =>
          None
      }

      res
    }

    isHomo(t1,t2)(Map())
  } // ensuring (res => res.isEmpty || isHomomorphic(t1, t2)(res.get))

  /** Checks whether two trees are homomoprhic modulo an identifier map.
    *
    * Used for transformation tests.
    */
  def isHomomorphic(t1: Expr, t2: Expr)(implicit map: Map[Identifier, Identifier]): Boolean = {
    object Same {
      def unapply(tt: (Expr, Expr)): Option[(Expr, Expr)] = {
        if (tt._1.getClass == tt._2.getClass) {
          Some(tt)
        } else {
          None
        }
      }
    }

    def idHomo(i1: Identifier, i2: Identifier)(implicit map: Map[Identifier, Identifier]) = {
      i1 == i2 || map.get(i1).contains(i2)
    }

    def fdHomo(fd1: FunDef, fd2: FunDef)(implicit map: Map[Identifier, Identifier]) = {
      (fd1.params.size == fd2.params.size) && {
         val newMap = map +
           (fd1.id -> fd2.id) ++
           (fd1.paramIds zip fd2.paramIds)
         isHomo(fd1.fullBody, fd2.fullBody)(newMap)
      }
    }

    def isHomo(t1: Expr, t2: Expr)(implicit map: Map[Identifier,Identifier]): Boolean = {

      def casesMatch(cs1 : Seq[MatchCase], cs2 : Seq[MatchCase]) : Boolean = {
        def patternHomo(p1: Pattern, p2: Pattern): (Boolean, Map[Identifier, Identifier]) = (p1, p2) match {
          case (InstanceOfPattern(ob1, cd1), InstanceOfPattern(ob2, cd2)) =>
            (ob1.size == ob2.size && cd1 == cd2, Map((ob1 zip ob2).toSeq : _*))

          case (WildcardPattern(ob1), WildcardPattern(ob2)) =>
            (ob1.size == ob2.size, Map((ob1 zip ob2).toSeq : _*))

          case (CaseClassPattern(ob1, ccd1, subs1), CaseClassPattern(ob2, ccd2, subs2)) =>
            val m = Map[Identifier, Identifier]() ++ (ob1 zip ob2)

            if (ob1.size == ob2.size && ccd1 == ccd2 && subs1.size == subs2.size) {
              (subs1 zip subs2).map { case (p1, p2) => patternHomo(p1, p2) }.foldLeft((true, m)) {
                case ((b1, m1), (b2,m2)) => (b1 && b2, m1 ++ m2)
              }
            } else {
              (false, Map())
            }

          case (UnapplyPattern(ob1, fd1, subs1), UnapplyPattern(ob2, fd2, subs2)) =>
            val m = Map[Identifier, Identifier]() ++ (ob1 zip ob2)

            if (ob1.size == ob2.size && fd1 == fd2 && subs1.size == subs2.size) {
              (subs1 zip subs2).map { case (p1, p2) => patternHomo(p1, p2) }.foldLeft((true, m)) {
                case ((b1, m1), (b2,m2)) => (b1 && b2, m1 ++ m2)
              }
            } else {
              (false, Map())
            }

          case (TuplePattern(ob1, subs1), TuplePattern(ob2, subs2)) =>
            val m = Map[Identifier, Identifier]() ++ (ob1 zip ob2)

            if (ob1.size == ob2.size && subs1.size == subs2.size) {
              (subs1 zip subs2).map { case (p1, p2) => patternHomo(p1, p2) }.foldLeft((true, m)) {
                case ((b1, m1), (b2,m2)) => (b1 && b2, m1 ++ m2)
              }
            } else {
              (false, Map())
            }

          case (LiteralPattern(ob1, lit1), LiteralPattern(ob2,lit2)) =>
            (ob1.size == ob2.size && lit1 == lit2, (ob1 zip ob2).toMap)

          case _ =>
            (false, Map())
        }

        (cs1 zip cs2).forall {
          case (MatchCase(p1, g1, e1), MatchCase(p2, g2, e2)) =>
            val (h, nm) = patternHomo(p1, p2)
            val g = (g1, g2) match {
              case (Some(g1), Some(g2)) => isHomo(g1,g2)(map ++ nm)
              case (None, None) => true
              case _ => false
            }
            val e = isHomo(e1, e2)(map ++ nm)

            g && e && h
        }

      }

      val res = (t1, t2) match {
        case (Variable(i1), Variable(i2)) =>
          idHomo(i1, i2)

        case (Let(id1, v1, e1), Let(id2, v2, e2)) =>
          isHomo(v1, v2) &&
          isHomo(e1, e2)(map + (id1 -> id2))

        case (LetDef(fds1, e1), LetDef(fds2, e2)) =>
          fds1.size == fds2.size &&
          {
            val zipped = fds1.zip(fds2)
            zipped.forall( fds =>
            fdHomo(fds._1, fds._2)
            ) &&
            isHomo(e1, e2)(map ++ zipped.map(fds => fds._1.id -> fds._2.id))
          }

        case (MatchExpr(s1, cs1), MatchExpr(s2, cs2)) =>
          cs1.size == cs2.size && isHomo(s1, s2) && casesMatch(cs1,cs2)

        case (Passes(in1, out1, cs1), Passes(in2, out2, cs2)) =>
          cs1.size == cs2.size && isHomo(in1,in2) && isHomo(out1,out2) && casesMatch(cs1,cs2)

        case (FunctionInvocation(tfd1, args1), FunctionInvocation(tfd2, args2)) =>
          // TODO: Check type params
          fdHomo(tfd1.fd, tfd2.fd) &&
          (args1 zip args2).forall{ case (a1, a2) => isHomo(a1, a2) }

        case Same(Deconstructor(es1, _), Deconstructor(es2, _)) =>
          (es1.size == es2.size) &&
          (es1 zip es2).forall{ case (e1, e2) => isHomo(e1, e2) }

        case _ =>
          false
      }

      res
    }

    isHomo(t1,t2)
  }

  /** Checks whether the match cases cover all possible inputs.
    *
    * Used when reconstructing pattern matching from ITE.
    *
    * e.g. The following:
    * {{{
    * list match {
    *   case Cons(_, Cons(_, a)) =>
    *
    *   case Cons(_, Nil) =>
    *
    *   case Nil =>
    *
    * }
    * }}}
    * is exaustive.
    *
    * @note Unused and unmaintained
    */
  def isMatchExhaustive(m: MatchExpr): Boolean = {

    /*
     * Takes the matrix of the cases per position/types:
     * e.g.
     * e match {   // Where e: (T1, T2, T3)
     *  case (P1, P2, P3) =>
     *  case (P4, P5, P6) =>
     *
     * becomes checked as:
     *   Seq( (T1, Seq(P1, P4)), (T2, Seq(P2, P5)), (T3, Seq(p3, p6)))
     *
     * We then check that P1+P4 covers every T1, etc..
     *
     * TODO: We ignore type parameters here, we might want to make sure it's
     * valid. What's Leon's semantics w.r.t. erasure?
     */
    def areExhaustive(pss: Seq[(TypeTree, Seq[Pattern])]): Boolean = pss.forall { case (tpe, ps) =>

      tpe match {
        case TupleType(tpes) =>
          val subs = ps.collect {
            case TuplePattern(_, bs) =>
              bs
          }

          areExhaustive(tpes zip subs.transpose)

        case _: ClassType =>

          def typesOf(tpe: TypeTree): Set[CaseClassDef] = tpe match {
            case AbstractClassType(ctp, _) =>
              ctp.knownDescendants.collect { case c: CaseClassDef => c }.toSet

            case CaseClassType(ctd, _) =>
              Set(ctd)

            case _ =>
              Set()
          }

          var subChecks = typesOf(tpe).map(_ -> Seq[Seq[Pattern]]()).toMap

          for (p <- ps) p match {
            case w: WildcardPattern =>
              // (a) Wildcard covers everything, no type left to check
              subChecks = Map.empty

            case InstanceOfPattern(_, cct) =>
              // (a: B) covers all Bs
              subChecks --= typesOf(cct)

            case CaseClassPattern(_, cct, subs) =>
              val ccd = cct.classDef
              // We record the patterns per types, if they still need to be checked
              if (subChecks contains ccd) {
                subChecks += (ccd -> (subChecks(ccd) :+ subs))
              }

            case _ =>
              sys.error("Unexpected case: "+p)
          }

          subChecks.forall { case (ccd, subs) =>
            val tpes = ccd.fields.map(_.getType)

            if (subs.isEmpty) {
              false
            } else {
              areExhaustive(tpes zip subs.transpose)
            }
          }

        case BooleanType =>
          // make sure ps contains either
          // - Wildcard or
          // - both true and false
          (ps exists { _.isInstanceOf[WildcardPattern] }) || {
            var found = Set[Boolean]()
            ps foreach {
              case LiteralPattern(_, BooleanLiteral(b)) => found += b
              case _ => ()
            }
            (found contains true) && (found contains false)
          }

        case UnitType =>
          // Anything matches ()
          ps.nonEmpty
        
        case StringType =>
          // Can't possibly pattern match against all Strings one by one
          ps exists (_.isInstanceOf[WildcardPattern])

        case Int32Type =>
          // Can't possibly pattern match against all Ints one by one
          ps exists (_.isInstanceOf[WildcardPattern])

        case _ =>
          true
      }
    }

    val patterns = m.cases.map {
      case SimpleCase(p, _) =>
        p
      case GuardedCase(p, _,  _) =>
        return false
    }

    areExhaustive(Seq((m.scrutinee.getType, patterns)))
  }

  /** Flattens a function that contains a LetDef with a direct call to it
    *
    * Used for merging synthesis results.
    *
    * {{{
    * def foo(a, b) {
    *   def bar(c, d) {
    *      if (..) { bar(c, d) } else { .. }
    *   }
    *   bar(b, a)
    * }
    * }}}
    * becomes
    * {{{
    * def foo(a, b) {
    *   if (..) { foo(b, a) } else { .. }
    * }
    * }}}
    */
  def flattenFunctions(fdOuter: FunDef, ctx: LeonContext, p: Program): FunDef = {
    fdOuter.body match {
      case Some(LetDef(fdsInner, FunctionInvocation(tfdInner2, args))) if fdsInner.size == 1 && fdsInner.head == tfdInner2.fd =>
        val fdInner = fdsInner.head
        val argsDef  = fdOuter.paramIds
        val argsCall = args.collect { case Variable(id) => id }

        if (argsDef.toSet == argsCall.toSet) {
          val defMap = argsDef.zipWithIndex.toMap
          val rewriteMap = argsCall.map(defMap)

          val innerIdsToOuterIds = (fdInner.paramIds zip argsCall).toMap

          def pre(e: Expr) = e match {
            case FunctionInvocation(tfd, args) if tfd.fd == fdInner =>
              val newArgs = (args zip rewriteMap).sortBy(_._2)
              FunctionInvocation(fdOuter.typed(tfd.tps), newArgs.map(_._1))
            case Variable(id) =>
              Variable(innerIdsToOuterIds.getOrElse(id, id))
            case _ =>
              e
          }

          def mergePre(outer: Option[Expr], inner: Option[Expr]): Option[Expr] = (outer, inner) match {
            case (None, Some(ie)) =>
              Some(simplePreTransform(pre)(ie))
            case (Some(oe), None) =>
              Some(oe)
            case (None, None) =>
              None
            case (Some(oe), Some(ie)) =>
              Some(and(oe, simplePreTransform(pre)(ie)))
          }

          def mergePost(outer: Option[Expr], inner: Option[Expr]): Option[Expr] = (outer, inner) match {
            case (None, Some(ie)) =>
              Some(simplePreTransform(pre)(ie))
            case (Some(oe), None) =>
              Some(oe)
            case (None, None) =>
              None
            case (Some(oe), Some(ie)) =>
              val res = FreshIdentifier("res", fdOuter.returnType, true)
              Some(Lambda(Seq(ValDef(res)), and(
                application(oe, Seq(Variable(res))),
                application(simplePreTransform(pre)(ie), Seq(Variable(res)))
              )))
          }

          val newFd = fdOuter.duplicate()

          val simp = Simplifiers.bestEffort(ctx, p)((_: Expr))

          newFd.body          = fdInner.body.map(b => simplePreTransform(pre)(b))
          newFd.precondition  = mergePre(fdOuter.precondition, fdInner.precondition).map(simp)
          newFd.postcondition = mergePost(fdOuter.postcondition, fdInner.postcondition).map(simp)

          newFd
        } else {
          fdOuter
        }
      case _ =>
        fdOuter
    }
  }

  def expandAndSimplifyArithmetic(expr: Expr): Expr = {
    val expr0 = try {
      val freeVars: Array[Identifier] = variablesOf(expr).toArray
      val coefs: Array[Expr] = TreeNormalizations.linearArithmeticForm(expr, freeVars)
      coefs.toList.zip(InfiniteIntegerLiteral(1) :: freeVars.toList.map(Variable)).foldLeft[Expr](InfiniteIntegerLiteral(0))((acc, t) => {
        if(t._1 == InfiniteIntegerLiteral(0)) acc else Plus(acc, Times(t._1, t._2))
      })
    } catch {
      case _: Throwable =>
        expr
    }
    simplifyArithmetic(expr0)
  }

  /* =================
   * Body manipulation
   * =================
   */

  /** Returns whether a particular [[Expressions.Expr]] contains specification
    * constructs, namely [[Expressions.Require]] and [[Expressions.Ensuring]].
    */
  def hasSpec(e: Expr): Boolean = exists {
    case Require(_, _) => true
    case Ensuring(_, _) => true
    case _ => false
  } (e)

  /** Merges the given [[Path]] into the provided [[Expressions.Expr]].
    *
    * This method expects to run on a [[Definitions.FunDef.fullBody]] and merges into
    * existing pre- and postconditions.
    *
    * @param expr The current body
    * @param path The path that should be wrapped around the given body
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPath(expr: Expr, path: Path): Expr = expr match {
    case Let(i, e, b) => withPath(b, path withBinding (i -> e))
    case Require(pre, b) => path specs (b, pre)
    case Ensuring(Require(pre, b), post) => path specs (b, pre, post)
    case Ensuring(b, post) => path specs (b, post = post)
    case b => path specs b
  }

  /** Replaces the precondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no precondition is provided, removes any existing precondition.
    * Else, wraps the expression with a [[Expressions.Require]] clause referring to the new precondition.
    *
    * @param expr The current expression
    * @param pred An optional precondition. Setting it to None removes any precondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPrecondition(expr: Expr, pred: Option[Expr]): Expr = (pred, expr) match {
    case (Some(newPre), Require(pre, b))              => req(newPre, b)
    case (Some(newPre), Ensuring(Require(pre, b), p)) => Ensuring(req(newPre, b), p)
    case (Some(newPre), Ensuring(b, p))               => Ensuring(req(newPre, b), p)
    case (Some(newPre), Let(i, e, b)) if hasSpec(b)   => Let(i, e, withPrecondition(b, pred))
    case (Some(newPre), b)                            => req(newPre, b)
    case (None, Require(pre, b))                      => b
    case (None, Ensuring(Require(pre, b), p))         => Ensuring(b, p)
    case (None, Let(i, e, b)) if hasSpec(b)           => Let(i, e, withPrecondition(b, pred))
    case (None, b)                                    => b
  }

  /** Replaces the postcondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no postcondition is provided, removes any existing postcondition.
    * Else, wraps the expression with a [[Expressions.Ensuring]] clause referring to the new postcondition.
    *
    * @param expr The current expression
    * @param oie An optional postcondition. Setting it to None removes any postcondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPostcondition(expr: Expr, oie: Option[Expr]): Expr = (oie, expr) match {
    case (Some(npost), Ensuring(b, post))          => ensur(b, npost)
    case (Some(npost), Let(i, e, b)) if hasSpec(b) => Let(i, e, withPostcondition(b, oie))
    case (Some(npost), b)                          => ensur(b, npost)
    case (None, Ensuring(b, p))                    => b
    case (None, Let(i, e, b)) if hasSpec(b)        => Let(i, e, withPostcondition(b, oie))
    case (None, b)                                 => b
  }

  /** Adds a body to a specification
    *
    * @param expr The specification expression [[Expressions.Ensuring]] or [[Expressions.Require]]. If none of these, the argument is discarded.
    * @param body An option of [[Expressions.Expr]] possibly containing an expression body.
    * @return The post/pre condition with the body. If no body is provided, returns [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withBody(expr: Expr, body: Option[Expr]): Expr = expr match {
    case Let(i, e, b) if hasSpec(b)      => Let(i, e, withBody(b, body))
    case Require(pre, _)                 => Require(pre, body.getOrElse(NoTree(expr.getType)))
    case Ensuring(Require(pre, _), post) => Ensuring(Require(pre, body.getOrElse(NoTree(expr.getType))), post)
    case Ensuring(_, post)               => Ensuring(body.getOrElse(NoTree(expr.getType)), post)
    case _                               => body.getOrElse(NoTree(expr.getType))
  }

  /** Extracts the body without its specification
    *
    * [[Expressions.Expr]] trees contain its specifications as part of certain nodes.
    * This function helps extracting only the body part of an expression
    *
    * @return An option type with the resulting expression if not [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withoutSpec(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                    => withoutSpec(b).map(Let(i, e, _))
    case Require(pre, b)                 => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(pre, b), post) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(b, post)               => Option(b).filterNot(_.isInstanceOf[NoTree])
    case b                               => Option(b).filterNot(_.isInstanceOf[NoTree])
  }

  /** Returns the precondition of an expression wrapped in Option */
  def preconditionOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                 => preconditionOf(b).map(Let(i, e, _))
    case Require(pre, _)              => Some(pre)
    case Ensuring(Require(pre, _), _) => Some(pre)
    case b                            => None
  }

  /** Returns the postcondition of an expression wrapped in Option */
  def postconditionOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)      => postconditionOf(b).map(Let(i, e, _))
    case Ensuring(_, post) => Some(post)
    case _                 => None
  }

  /** Returns a tuple of precondition, the raw body and the postcondition of an expression */
  def breakDownSpecs(e : Expr) = (preconditionOf(e), withoutSpec(e), postconditionOf(e))

  def preTraversalWithParent(f: (Expr, Option[Tree]) => Unit, initParent: Option[Tree] = None)(e: Expr): Unit = {
    val rec = preTraversalWithParent(f, Some(e)) _

    f(e, initParent)

    val Deconstructor(es, _) = e
    es foreach rec
  }

  object InvocationExtractor {
    private def flatInvocation(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
      case fi @ FunctionInvocation(tfd, args) => Some((tfd, args))
      case Application(caller, args) => flatInvocation(caller) match {
        case Some((tfd, prevArgs)) => Some((tfd, prevArgs ++ args))
        case None => None
      }
        case _ => None
    }

    def unapply(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
      case IsTyped(f: FunctionInvocation, ft: FunctionType) => None
      case IsTyped(f: Application, ft: FunctionType) => None
      case FunctionInvocation(tfd, args) => Some(tfd -> args)
      case f: Application => flatInvocation(f)
      case _ => None
    }
  }

  def firstOrderCallsOf(expr: Expr): Set[(TypedFunDef, Seq[Expr])] =
    collect[(TypedFunDef, Seq[Expr])] {
      case InvocationExtractor(tfd, args) => Set(tfd -> args)
      case _ => Set.empty
    }(expr)

  object ApplicationExtractor {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, _) => None
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
  }
        case Application(caller, args) => Some((caller, args))
        case _ => None
    }

    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case IsTyped(f: Application, ft: FunctionType) => None
      case f: Application => flatApplication(f)
      case _ => None
    }
  }

  def firstOrderAppsOf(expr: Expr): Set[(Expr, Seq[Expr])] =
    collect[(Expr, Seq[Expr])] {
      case ApplicationExtractor(caller, args) => Set(caller -> args)
      case _ => Set.empty
    } (expr)

  def simplifyHOFunctions(expr: Expr) : Expr = {

    def liftToLambdas(expr: Expr) = {
      def apply(expr: Expr, args: Seq[Expr]): Expr = expr match {
        case IfExpr(cond, thenn, elze) =>
          IfExpr(cond, apply(thenn, args), apply(elze, args))
        case Let(i, e, b) =>
          Let(i, e, apply(b, args))
        case LetTuple(is, es, b) =>
          letTuple(is, es, apply(b, args))
        //case l @ Lambda(params, body) =>
        //  l.withParamSubst(args, body)
        case _ => Application(expr, args)
      }

      def lift(expr: Expr): Expr = expr.getType match {
        case FunctionType(from, to) => expr match {
          case _ : Lambda => expr
          case _ : Variable => expr
          case e =>
            val args = from.map(tpe => ValDef(FreshIdentifier("x", tpe, true)))
            val application = apply(expr, args.map(_.toVariable))
            Lambda(args, lift(application))
        }
        case _ => expr
      }

      def extract(expr: Expr, build: Boolean) = if (build) lift(expr) else expr

      def rec(expr: Expr, build: Boolean): Expr = expr match {
        case Application(caller, args) =>
          val newArgs = args.map(rec(_, true))
          val newCaller = rec(caller, false)
          extract(Application(newCaller, newArgs), build)
        case FunctionInvocation(fd, args) =>
          val newArgs = args.map(rec(_, true))
          extract(FunctionInvocation(fd, newArgs), build)
        case l @ Lambda(args, body) =>
          val newBody = rec(body, true)
          extract(Lambda(args, newBody), build)
        case Deconstructor(es, recons) => recons(es.map(rec(_, build)))
      }

      rec(lift(expr), true)
    }

    liftToLambdas(
      matchToIfThenElse(
        expr
      )
    )
  }

  /** lift closures introduced by synthesis.
    *
    * Closures already define all
    * the necessary information as arguments, no need to close them.
    */
  def liftClosures(e: Expr): (Set[FunDef], Expr) = {
    var fds: Map[FunDef, FunDef] = Map()

    val res1 = preMap({
      case LetDef(lfds, b) =>
        val nfds = lfds.map(fd => fd -> fd.duplicate())

        fds ++= nfds

        Some(letDef(nfds.map(_._2), b))

      case FunctionInvocation(tfd, args) =>
        if (fds contains tfd.fd) {
          Some(FunctionInvocation(fds(tfd.fd).typed(tfd.tps), args))
        } else {
          None
        }

      case _ =>
        None
    })(e)

    // we now remove LetDefs
    val res2 = preMap({
      case LetDef(fds, b) =>
        Some(b)
      case _ =>
        None
    }, applyRec = true)(res1)

    (fds.values.toSet, res2)
  }

  def isListLiteral(e: Expr)(implicit pgm: Program): Option[(TypeTree, List[Expr])] = e match {
    case CaseClass(CaseClassType(classDef, Seq(tp)), Nil) =>
      for {
        leonNil <- pgm.library.Nil
        if classDef == leonNil
      } yield {
        (tp, Nil)
      }
    case CaseClass(CaseClassType(classDef, Seq(tp)), Seq(hd, tl)) =>
      for {
        leonCons <- pgm.library.Cons
        if classDef == leonCons
        (_, tlElems) <- isListLiteral(tl)
      } yield {
        (tp, hd :: tlElems)
      }
    case _ =>
      None
  }


  /** Collects from within an expression all conditions under which the evaluation of the expression
    * will not fail (e.g. by violating a function precondition or evaluating to an error).
    *
    * Collection of preconditions of function invocations can be disabled
    * (mainly for [[leon.verification.Tactic]]).
    *
    * @param e The expression for which correctness conditions are calculated.
    * @param collectFIs Whether we also want to collect preconditions for function invocations
    * @return A sequence of pairs (expression, condition)
    */
  def collectCorrectnessConditions(e: Expr, collectFIs: Boolean = false): Seq[(Expr, Expr)] = {
    val conds = collectWithPC {

      case m @ MatchExpr(scrut, cases) =>
        (m, orJoin(cases map (matchCaseCondition(scrut, _).toClause)))

      case e @ Error(_, _) =>
        (e, BooleanLiteral(false))

      case a @ Assert(cond, _, _) =>
        (a, cond)

      /*case e @ Ensuring(body, post) =>
        (e, application(post, Seq(body)))

      case r @ Require(pred, e) =>
        (r, pred)*/

      case fi @ FunctionInvocation(tfd, args) if tfd.hasPrecondition && collectFIs =>
        (fi, tfd.withParamSubst(args, tfd.precondition.get))
    }(e)

    conds map {
      case ((e, cond), path) =>
        (e, path implies cond)
    }
  }


  def simpleCorrectnessCond(e: Expr, path: Path, sf: SolverFactory[Solver]): Expr = {
    simplifyPaths(sf, path)(
      andJoin( collectCorrectnessConditions(e) map { _._2 } )
    )
  }

  def tupleWrapArg(fun: Expr) = fun.getType match {
    case FunctionType(args, res) if args.size > 1 =>
      val newArgs = fun match {
        case Lambda(args, _) => args map (_.id)
        case _ => args map (arg => FreshIdentifier("x", arg.getType, alwaysShowUniqueID = true))
      }
      val res = FreshIdentifier("res", TupleType(args map (_.getType)), alwaysShowUniqueID = true)
      val patt = TuplePattern(None, newArgs map (arg => WildcardPattern(Some(arg))))
      Lambda(Seq(ValDef(res)), MatchExpr(res.toVariable, Seq(SimpleCase(patt, application(fun, newArgs map (_.toVariable))))))
    case _ =>
      fun
  }
  
  // Use this only to debug isValueOfType
  private implicit class BooleanAdder(b: Boolean) {
    @inline def <(msg: String) = {/*if(!b) println(msg); */b}
  }

  /** Returns true if expr is a value of type t */
  def isValueOfType(e: Expr, t: TypeTree): Boolean = {
    def unWrapSome(s: Expr) = s match {
      case CaseClass(_, Seq(a)) => a
      case _ => s
    }
    (e, t) match {
      case (StringLiteral(_), StringType) => true
      case (IntLiteral(_), Int32Type) => true
      case (InfiniteIntegerLiteral(_), IntegerType) => true
      case (CharLiteral(_), CharType) => true
      case (FractionalLiteral(_, _), RealType) => true
      case (BooleanLiteral(_), BooleanType) => true
      case (UnitLiteral(), UnitType) => true
      case (GenericValue(t, _), tp) => t == tp
      case (Tuple(elems), TupleType(bases)) =>
        elems zip bases forall (eb => isValueOfType(eb._1, eb._2))
      case (FiniteSet(elems, tbase), SetType(base)) =>
        tbase == base &&
        (elems forall isValue)
      case (FiniteMap(elems, tk, tv), MapType(from, to)) =>
        (tk == from) < s"$tk not equal to $from" && (tv == to) < s"$tv not equal to $to" &&
        (elems forall (kv => isValueOfType(kv._1, from) < s"${kv._1} not a value of type ${from}" && isValueOfType(unWrapSome(kv._2), to) < s"${unWrapSome(kv._2)} not a value of type ${to}" ))
      case (NonemptyArray(elems, defaultValues), ArrayType(base)) =>
        elems.values forall (x => isValueOfType(x, base))
      case (EmptyArray(tpe), ArrayType(base)) =>
        tpe == base
      case (CaseClass(ct, args), ct2@AbstractClassType(classDef, tps)) => 
        TypeOps.isSubtypeOf(ct, ct2) < s"$ct not a subtype of $ct2" &&
        ((args zip ct.fieldsTypes) forall (argstyped => isValueOfType(argstyped._1, argstyped._2) < s"${argstyped._1} not a value of type ${argstyped._2}" ))
      case (CaseClass(ct, args), ct2@CaseClassType(classDef, tps)) => 
        (ct == ct2) <  s"$ct not equal to $ct2" &&
        ((args zip ct.fieldsTypes) forall (argstyped => isValueOfType(argstyped._1, argstyped._2)))
      case (FiniteLambda(mapping, default, tpe), exTpe@FunctionType(ins, out)) =>
        variablesOf(e).isEmpty &&
        tpe == exTpe
      case (Lambda(valdefs, body), FunctionType(ins, out)) =>
        variablesOf(e).isEmpty &&
        (valdefs zip ins forall (vdin => TypeOps.isSubtypeOf(vdin._2, vdin._1.getType) < s"${vdin._2} is not a subtype of ${vdin._1.getType}")) &&
        (TypeOps.isSubtypeOf(body.getType, out)) < s"${body.getType} is not a subtype of ${out}"
      case (FiniteBag(elements, fbtpe), BagType(tpe)) =>
        fbtpe == tpe && elements.forall{ case (key, value) => isValueOfType(key, tpe) && isValueOfType(value, IntegerType) }
      case _ => false
    }
  }
    
  /** Returns true if expr is a value. Stronger than isGround */
  val isValue = (e: Expr) => isValueOfType(e, e.getType)
  
  /** Returns a nested string explaining why this expression is typed the way it is.*/
  def explainTyping(e: Expr): String = {
    leon.purescala.ExprOps.fold[String]{ (e, se) => 
      e match {
        case FunctionInvocation(tfd, args) =>
          s"$e is of type ${e.getType}" + se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString + s" because ${tfd.fd.id.name} was instantiated with ${tfd.fd.tparams.zip(args).map(k => k._1 +":="+k._2).mkString(",")} with type ${tfd.fd.params.map(_.getType).mkString(",")} => ${tfd.fd.returnType}"
        case e =>
          s"$e is of type ${e.getType}" + se.map(child => "\n  " + "\n".r.replaceAllIn(child, "\n  ")).mkString
      }
    }(e)
  }
}
