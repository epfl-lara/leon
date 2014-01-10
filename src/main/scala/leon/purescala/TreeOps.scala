/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

import leon.solvers._

import scala.collection.concurrent.TrieMap

object TreeOps {
  import Common._
  import TypeTrees._
  import Definitions._
  import Trees._
  import Extractors._

  /**
   * Core API
   * ========
   *
   * All these functions should be stable, tested, and used everywhere. Modify
   * with care.
   */


  /**
   * Do a right tree fold
   *
   * f takes the current node, as well as the seq of results form the subtrees.
   *
   * Usages of views makes the computation lazy. (which is useful for
   * contains-like operations)
   */
  def foldRight[T](f: (Expr, Seq[T]) => T)(e: Expr): T = {
    val rec = foldRight(f) _

    e match {
      case t: Terminal =>
        f(t, Stream.empty)

      case u @ UnaryOperator(e, builder) =>
        f(u, List(e).view.map(rec))

      case b @ BinaryOperator(e1, e2, builder) =>
        f(b, List(e1, e2).view.map(rec))

      case n @ NAryOperator(es, builder) =>
        f(n, es.view.map(rec))
    }
  }

  /**
   * pre-traversal of the tree, calls f() on every node *before* visiting
   * children.
   *
   * e.g.
   *
   *   Add(a, Minus(b, c))
   *
   * will yield, in order:
   *
   *   f(Add(a, Minus(b, c))), f(a), f(Minus(b, c)), f(b), f(c)
   */
  def preTraversal(f: Expr => Unit)(e: Expr): Unit = {
    val rec = preTraversal(f) _
    f(e)

    e match {
      case t: Terminal =>

      case u @ UnaryOperator(e, builder) =>
        List(e).foreach(rec)

      case b @ BinaryOperator(e1, e2, builder) =>
        List(e1, e2).foreach(rec)

      case n @ NAryOperator(es, builder) =>
        es.foreach(rec)
    }
  }

  /**
   * post-traversal of the tree, calls f() on every node *after* visiting
   * children.
   *
   * e.g.
   *
   *   Add(a, Minus(b, c))
   *
   * will yield, in order:
   *
   *   f(a), f(b), f(c), f(Minus(b, c)), f(Add(a, Minus(b, c)))
   */
  def postTraversal(f: Expr => Unit)(e: Expr): Unit = {
    val rec = preTraversal(f) _

    e match {
      case t: Terminal =>

      case u @ UnaryOperator(e, builder) =>
        List(e).foreach(rec)

      case b @ BinaryOperator(e1, e2, builder) =>
        List(e1, e2).foreach(rec)

      case n @ NAryOperator(es, builder) =>
        es.foreach(rec)
    }

    f(e)
  }

  /**
   * pre-transformation of the tree, takes a partial function of replacements.
   * Substitutes *before* recursing down the trees.
   *
   * e.g.
   *
   *   Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
   *
   * will yield:
   *
   *   Add(a, d)   // And not Add(a, f) because it only substitute once for each level.
   */
  def preMap(f: Expr => Option[Expr])(e: Expr): Expr = {
    val rec = preMap(f) _

    val newV = f(e).getOrElse(e)

    newV match {
      case u @ UnaryOperator(e, builder) =>
        val newE = rec(e)

        if (newE ne e) {
          builder(newE).copiedFrom(u)
        } else {
          u
        }

      case b @ BinaryOperator(e1, e2, builder) =>
        val newE1 = rec(e1)
        val newE2 = rec(e2)

        if ((newE1 ne e1) || (newE2 ne e2)) {
          builder(newE1, newE2).copiedFrom(b)
        } else {
          b
        }

      case n @ NAryOperator(es, builder) =>
        val newEs = es.map(rec)

        if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
          builder(newEs).copiedFrom(n)
        } else {
          n
        }

      case t: Terminal =>
        t
    }
  }

  /**
   * post-transformation of the tree, takes a partial function of replacements.
   * Substitutes *after* recursing down the trees.
   *
   * e.g.
   *
   *   Add(a, Minus(b, c)) with replacements: Minus(b,c) -> d, b -> e, d -> f
   *
   * will yield:
   *
   *   Add(a, Minus(e, c))
   */
  def postMap(f: Expr => Option[Expr])(e: Expr): Expr = {
    val rec = postMap(f) _

    val newV = e match {
      case u @ UnaryOperator(e, builder) =>
        val newE = rec(e)

        if (newE ne e) {
          builder(newE).copiedFrom(u)
        } else {
          u
        }

      case b @ BinaryOperator(e1, e2, builder) =>
        val newE1 = rec(e1)
        val newE2 = rec(e2)

        if ((newE1 ne e1) || (newE2 ne e2)) {
          builder(newE1, newE2).copiedFrom(b)
        } else {
          b
        }

      case n @ NAryOperator(es, builder) =>
        val newEs = es.map(rec)

        if ((newEs zip es).exists { case (bef, aft) => aft ne bef }) {
          builder(newEs).copiedFrom(n)
        } else {
          n
        }

      case t: Terminal =>
        t
    }

    f(newV).getOrElse(newV)
  }

  /*
   * Apply 'f' on 'e' as long as until it stays the same (value equality)
   */
  def fixpoint[T](f: T => T)(e: T): T = {
    var v1 = e
    var v2 = f(v1)
    while(v2 != v1) {
      v1 = v2
      v2 = f(v2)
    }
    v2
  }

  ///*
  // * Turn a total function returning Option[A] into a partial function
  // * returning A.
  // * Optimize for isDefinedAt -> apply access pattern
  // */
  //def unlift[A, B](f: A => Option[B]): PartialFunction[A,B] = new PartialFunction[A, B] {
  //  var last: Option[(A, Option[B])] = None

  //  def apply(a: A) = last match {
  //    case Some((a2, res)) if a2 == a => res.get
  //    case _ => f(a).get
  //  }

  //  def isDefinedAt(a: A) = {
  //    val res = f(a)
  //    last = Some((a, res))
  //    res.isDefined
  //  }
  //}

  /**
   * Auxiliary API
   * =============
   *
   * Convenient methods using the Core API.
   */


  /**
   * Returns true if matcher(se) == true where se is any sub-expression of e
   */

  def exists(matcher: Expr => Boolean)(e: Expr): Boolean = {
    foldRight[Boolean]({ (e, subs) =>  matcher(e) || subs.contains(true) } )(e)
  }

  def collect[T](matcher: Expr => Set[T])(e: Expr): Set[T] = {
    foldRight[Set[T]]({ (e, subs) => matcher(e) ++ subs.foldLeft(Set[T]())(_ ++ _) } )(e)
  }

  def filter(matcher: Expr => Boolean)(e: Expr): Set[Expr] = {
    collect[Expr] { e => if (matcher(e)) Set(e) else Set() }(e)
  }

  def count(matcher: Expr => Int)(e: Expr): Int = {
    foldRight[Int]({ (e, subs) =>  matcher(e) + subs.foldLeft(0)(_ + _) } )(e)
  }

  def replace(substs: Map[Expr,Expr], expr: Expr) : Expr = {
    postMap(substs.lift)(expr)
  }

  def replaceFromIDs(substs: Map[Identifier, Expr], expr: Expr) : Expr = {
    postMap( {
        case Variable(i) => substs.get(i)
        case _ => None
    })(expr)
  }

  def variablesOf(expr: Expr): Set[Identifier] = {
    foldRight[Set[Identifier]]({
      case (e, subs) =>
        val subvs = subs.foldLeft(Set[Identifier]())(_ ++ _)

        e match {
          case Variable(i) => subvs + i
          case Let(i,_,_) => subvs - i
          case Choose(is,_) => subvs -- is
          case MatchExpr(_, cses) => subvs -- (cses.map(_.pattern.binders).foldLeft(Set[Identifier]())((a, b) => a ++ b))
          case _ => subvs
        }
    })(expr)
  }

  def containsFunctionCalls(expr: Expr): Boolean = {
    exists{
        case _: FunctionInvocation => true
        case _ => false
    }(expr)
  }

  /**
   * Returns all Function calls found in an expression
   */
  def functionCallsOf(expr: Expr): Set[FunctionInvocation] = {
    foldRight[Set[FunctionInvocation]]({
      case (e, subs) =>
        val c: Set[FunctionInvocation] = e match {
          case f: FunctionInvocation => Set(f)
          case _ => Set()
        }
        subs.foldLeft(c)(_ ++ _)
    })(expr)
  }
  def negate(expr: Expr) : Expr = (expr match {
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
  }).setType(expr.getType).setPos(expr)

  // rewrites pattern-matching expressions to use fresh variables for the binders
  def freshenLocals(expr: Expr) : Expr = {
    def rewritePattern(p: Pattern, sm: Map[Identifier,Identifier]) : Pattern = p match {
      case InstanceOfPattern(Some(b), ctd) => InstanceOfPattern(Some(sm(b)), ctd)
      case WildcardPattern(Some(b)) => WildcardPattern(Some(sm(b)))
      case TuplePattern(ob, sps) => TuplePattern(ob.map(sm(_)), sps.map(rewritePattern(_, sm)))
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


    postMap({
      case m @ MatchExpr(s, cses) =>
        Some(MatchExpr(s, cses.map(freshenCase(_))).copiedFrom(m))

      case l @ Let(i,e,b) =>
        val newID = FreshIdentifier(i.name, true).copiedFrom(i)
        Some(Let(newID, e, replace(Map(Variable(i) -> Variable(newID)), b)))

      case _ => None
    })(expr)
  }

  /**
   * Simplifies let expressions:
   *  - removes lets when expression never occurs
   *  - simplifies when expressions occurs exactly once
   *  - expands when expression is just a variable.
   * Note that the code is simple but far from optimal (many traversals...)
   */
  def simplifyLets(expr: Expr) : Expr = {
    def simplerLet(t: Expr) : Option[Expr] = t match {

      case letExpr @ Let(i, t: Terminal, b) if !containsChoose(b) =>
        Some(replace(Map((Variable(i) -> t)), b))

      case letExpr @ Let(i,e,b) if !containsChoose(b) => {
        val occurences = count{ (e: Expr) => e match {
          case Variable(x) if x == i => 1
          case _ => 0
        }}(b)

        if(occurences == 0) {
          Some(b)
        } else if(occurences == 1) {
          Some(replace(Map((Variable(i) -> e)), b))
        } else {
          None
        }
      }

      case letTuple @ LetTuple(ids, Tuple(exprs), body) if !containsChoose(body) =>
        var newBody = body

        val (remIds, remExprs) = (ids zip exprs).filter { 
          case (id, value: Terminal) =>
            newBody = replace(Map((Variable(id) -> value)), newBody)
            //we replace, so we drop old
            false
          case (id, value) =>
            val occurences = count{ (e: Expr) => e match {
              case Variable(x) if x == id => 1
              case _ => 0
            }}(body)

            if(occurences == 0) {
              false
            } else if(occurences == 1) {
              newBody = replace(Map((Variable(id) -> value)), newBody)
              false
            } else {
              true
            }
        }.unzip


        if (remIds.isEmpty) {
          Some(newBody)
        } else if (remIds.tail.isEmpty) {
          Some(Let(remIds.head, remExprs.head, newBody))
        } else {
          Some(LetTuple(remIds, Tuple(remExprs), newBody))
        }

      case l @ LetTuple(ids, tExpr: Terminal, body) if !containsChoose(body) =>
        val substMap : Map[Expr,Expr] = ids.map(Variable(_) : Expr).zipWithIndex.toMap.map {
          case (v,i) => (v -> TupleSelect(tExpr, i + 1).copiedFrom(v))
        }

        Some(replace(substMap, body))

      case l @ LetTuple(ids, tExpr, body) if !containsChoose(body) =>
        val arity = ids.size
        val zeroVec = Seq.fill(arity)(0)
        val idMap   = ids.zipWithIndex.toMap.mapValues(i => zeroVec.updated(i, 1))

        // A map containing vectors of the form (0, ..., 1, ..., 0) where
        // the one corresponds to the index of the identifier in the
        // LetTuple. The idea is that we can sum such vectors up to compute
        // the occurences of all variables in one traversal of the
        // expression.

        val occurences : Seq[Int] = foldRight[Seq[Int]]({ case (e, subs) =>
          e match {
            case Variable(x) => idMap.getOrElse(x, zeroVec)
            case _ => subs.foldLeft(zeroVec) { case (a1, a2) =>
                (a1 zip a2).map(p => p._1 + p._2)
              }
          }
        })(body)

        val total = occurences.sum

        if(total == 0) {
          Some(body)
        } else if(total == 1) {
          val substMap : Map[Expr,Expr] = ids.map(Variable(_) : Expr).zipWithIndex.toMap.map {
            case (v,i) => (v -> TupleSelect(tExpr, i + 1).copiedFrom(v))
          }

          Some(replace(substMap, body))
        } else {
          None
        }

      case _ => None
    }

    postMap(simplerLet)(expr)
  }

  /* Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut, s), cses.map(inCase(_, s))).setType(m.getType).setPos(m)
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

  /** Rewrites all pattern-matching expressions into if-then-else expressions,
   * with additional error conditions. Does not introduce additional variables.
   */
  val cacheMtITE = new TrieMap[Expr, Expr]()

  def matchToIfThenElse(expr: Expr) : Expr = {
    cacheMtITE.get(expr) match {
      case Some(res) =>
        res
      case None =>
        val r = convertMatchToIfThenElse(expr)
        cacheMtITE += expr -> r
        r
    }
  }

  def conditionForPattern(in: Expr, pattern: Pattern, includeBinders: Boolean = false) : Expr = {
    def bind(ob: Option[Identifier], to: Expr): Expr = {
      if (!includeBinders) {
        BooleanLiteral(true)
      } else {
        ob.map(id => Equals(Variable(id), to)).getOrElse(BooleanLiteral(true))
      }
    }

    def rec(in: Expr, pattern: Pattern): Expr = {
      pattern match {
        case WildcardPattern(ob) => bind(ob, in)
        case InstanceOfPattern(ob, ct) =>
          ct match {
            case _: AbstractClassDef =>
              bind(ob, in)

            case cd: CaseClassDef =>
              And(CaseClassInstanceOf(cd, in), bind(ob, in))
          }
        case CaseClassPattern(ob, ccd, subps) => {
          assert(ccd.fields.size == subps.size)
          val pairs = ccd.fields.map(_.id).toList zip subps.toList
          val subTests = pairs.map(p => rec(CaseClassSelector(ccd, in, p._1), p._2))
          val together = And(bind(ob, in) +: subTests)
          And(CaseClassInstanceOf(ccd, in), together)
        }
        case TuplePattern(ob, subps) => {
          val TupleType(tpes) = in.getType
          assert(tpes.size == subps.size)
          val subTests = subps.zipWithIndex.map{case (p, i) => rec(TupleSelect(in, i+1).setType(tpes(i)), p)}
          And(bind(ob, in) +: subTests)
        }
      }
    }

    rec(in, pattern)
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
          val patCond = conditionForPattern(scrut, cse.pattern, includeBinders = false)
          val realCond = cse.theGuard match {
            case Some(g) => And(patCond, replaceFromIDs(map, g))
            case None => patCond
          }
          val newRhs = replaceFromIDs(map, cse.rhs)
          (realCond, newRhs)
        }

        val bigIte = condsAndRhs.foldRight[Expr](Error("non-exhaustive match").setType(bestRealType(m.getType)).setPos(m))((p1, ex) => {
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

    postMap(rewritePM)(expr)
  }

  /**
   * Rewrites all map accesses with additional error conditions.
   */
  val cacheMGWC = new TrieMap[Expr, Expr]()

  def mapGetWithChecks(expr: Expr) : Expr = {
    cacheMGWC.get(expr) match {
      case Some(res) =>
        res
      case None =>

        val r = postMap({
          case mg @ MapGet(m,k) =>
            val ida = MapIsDefinedAt(m, k)
            Some(IfExpr(ida, mg, Error("key not found for map access").copiedFrom(mg)).copiedFrom(mg))

          case _=>
            None
        })(expr)

        cacheMGWC += expr -> r
        r
    }
  }

  /**
   * Returns simplest value of a given type
   */
  def simplestValue(tpe: TypeTree) : Expr = tpe match {
    case Int32Type                  => IntLiteral(0)
    case BooleanType                => BooleanLiteral(false)
    case SetType(baseType)          => FiniteSet(Seq()).setType(tpe)
    case MapType(fromType, toType)  => FiniteMap(Seq()).setType(tpe)
    case TupleType(tpes)            => Tuple(tpes.map(simplestValue))
    case ArrayType(tpe)             => ArrayFill(IntLiteral(0), simplestValue(tpe))

    case AbstractClassType(acd) =>
      val children = acd.knownChildren

      def isRecursive(ccd: CaseClassDef): Boolean = {
        ccd.fields.exists(fd => fd.getType match {
          case AbstractClassType(fieldAcd) => acd == fieldAcd
          case CaseClassType(fieldCcd) => ccd == fieldCcd
          case _ => false
        })
      }

      val nonRecChildren = children.collect { case ccd: CaseClassDef if !isRecursive(ccd) => ccd }

      val orderedChildren = nonRecChildren.sortBy(_.fields.size)

      simplestValue(classDefToClassType(orderedChildren.head))

    case CaseClassType(ccd) =>
      val fields = ccd.fields
      CaseClass(ccd, fields.map(f => simplestValue(f.getType)))

    case _ => throw new Exception("I can't choose simplest value for type " + tpe)
  }

  /**
   * Guarentees that all IfExpr will be at the top level and as soon as you
   * encounter a non-IfExpr, then no more IfExpr can be found in the
   * sub-expressions
   *
   * Assumes no match expressions
   */
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(IfExpr(c, t, e), op) =>
        Some(IfExpr(c, op(t).copiedFrom(uop), op(e).copiedFrom(uop)).copiedFrom(uop))

      case bop@BinaryOperator(IfExpr(c, t, e), t2, op) =>
        Some(IfExpr(c, op(t, t2).copiedFrom(bop), op(e, t2).copiedFrom(bop)).copiedFrom(bop))

      case bop@BinaryOperator(t1, IfExpr(c, t, e), op) =>
        Some(IfExpr(c, op(t1, t).copiedFrom(bop), op(t1, e).copiedFrom(bop)).copiedFrom(bop))

      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).copiedFrom(nop),
            op(beforeIte ++ Seq(e) ++ afterIte).copiedFrom(nop)
          ).setType(nop.getType))
        }
      }
      case _ => None
    }

    fixpoint(postMap(transform))(expr)
  }

  def genericTransform[C](pre:  (Expr, C) => (Expr, C),
                          post: (Expr, C) => (Expr, C),
                          combiner: (Seq[C]) => C)(init: C)(expr: Expr) = {

    def rec(eIn: Expr, cIn: C): (Expr, C) = {

      val (expr, ctx) = pre(eIn, cIn)

      val (newExpr, newC) = expr match {
        case t: Terminal =>
          (expr, cIn)

        case UnaryOperator(e, builder) =>
          val (e1, c) = rec(e, ctx)
          val newE = builder(e1).copiedFrom(expr)

          (newE, combiner(Seq(c)))

        case BinaryOperator(e1, e2, builder) =>
          val (ne1, c1) = rec(e1, ctx)
          val (ne2, c2) = rec(e2, ctx)
          val newE = builder(ne1, ne2).copiedFrom(expr)

          (newE, combiner(Seq(c1, c2)))

        case NAryOperator(es, builder) =>
          val (nes, cs) = es.map{ rec(_, ctx)}.unzip
          val newE = builder(nes).copiedFrom(expr)

          (newE, combiner(cs))

        case e =>
          sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
      }

      post(newExpr, newC)
    }

    rec(expr, init)
  }

  private def noCombiner(subCs: Seq[Unit]) = ()

  def simpleTransform(pre: Expr => Expr, post: Expr => Expr)(expr: Expr) = {
    val newPre  = (e: Expr, c: Unit) => (pre(e), ())
    val newPost = (e: Expr, c: Unit) => (post(e), ())

    genericTransform[Unit](newPre, newPost, noCombiner)(())(expr)._1
  }

  def simplePreTransform(pre: Expr => Expr)(expr: Expr) = {
    val newPre  = (e: Expr, c: Unit) => (pre(e), ())

    genericTransform[Unit](newPre, (_, _), noCombiner)(())(expr)._1
  }

  def simplePostTransform(post: Expr => Expr)(expr: Expr) = {
    val newPost = (e: Expr, c: Unit) => (post(e), ())

    genericTransform[Unit]((e,c) => (e, None), newPost, noCombiner)(())(expr)._1
  }

  /*
   * Transforms complicated Ifs into multiple nested if blocks
   * It will decompose every OR clauses, and it will group AND clauses checking
   * isInstanceOf toghether.
   *
   *  if (a.isInstanceof[T1] && a.tail.isInstanceof[T2] && a.head == a2 || C) {
   *     T
   *  } else {
   *     E
   *  }
   *
   * Becomes:
   *
   *  if (a.isInstanceof[T1] && a.tail.isInstanceof[T2]) {
   *    if (a.head == a2) {
   *      T
   *    } else {
   *      if(C) {
   *        T
   *      } else {
   *        E
   *      }
   *    }
   *  } else {
   *    if(C) {
   *      T
   *    } else {
   *      E
   *    }
   *  }
   * 
   * This transformation runs immediately before patternMatchReconstruction.
   *
   * Notes: positions are lost.
   */
  def decomposeIfs(e: Expr): Expr = {
    def pre(e: Expr): Expr = e match {
      case IfExpr(cond, thenn, elze) =>
        val TopLevelOrs(orcases) = cond

        if (orcases.exists{ case TopLevelAnds(ands) => ands.exists(_.isInstanceOf[CaseClassInstanceOf]) } ) {
          if (!orcases.tail.isEmpty) {
            pre(IfExpr(orcases.head, thenn, IfExpr(Or(orcases.tail), thenn, elze)))
          } else {
            val TopLevelAnds(andcases) = orcases.head

            val (andis, andnotis) = andcases.partition(_.isInstanceOf[CaseClassInstanceOf])

            if (andis.isEmpty || andnotis.isEmpty) {
              e
            } else {
              IfExpr(And(andis), IfExpr(And(andnotis), thenn, elze), elze)
            }
          }
        } else {
          e
        }
      case _ =>
        e
    }

    simplePreTransform(pre)(e)
  }

  /**
   * Reconstructs match expressions from if-then-elses.
   *
   * Notes: positions are lost.
   */
  def patternMatchReconstruction(e: Expr): Expr = {
    def post(e: Expr): Expr = e match {
      case IfExpr(cond, thenn, elze) =>
        val TopLevelAnds(cases) = cond

        if (cases.forall(_.isInstanceOf[CaseClassInstanceOf])) {
          // matchingOn might initially be: a : T1, a.tail : T2, b: T2
          def selectorDepth(e: Expr): Int = e match {
            case cd: CaseClassSelector =>
              1+selectorDepth(cd.caseClass)
            case _ =>
              0
          }

          var scrutSet = Set[Expr]()
          var conditions = Map[Expr, CaseClassDef]()

          var matchingOn = cases.collect { case cc : CaseClassInstanceOf => cc } sortBy(cc => selectorDepth(cc.expr))
          for (CaseClassInstanceOf(cd, expr) <- matchingOn) {
            conditions += expr -> cd

            expr match {
              case cd: CaseClassSelector =>
                if (!scrutSet.contains(cd.caseClass)) {
                  // we found a test looking like "a.foo.isInstanceof[..]"
                  // without a check on "a".
                  scrutSet += cd
                }
              case e =>
                scrutSet += e
            }
          }

          var substMap = Map[Expr, Expr]()

          def computePatternFor(cd: CaseClassDef, prefix: Expr): Pattern = {

            val name = prefix match {
              case CaseClassSelector(_, _, id) => id.name
              case Variable(id) => id.name
              case _ => "tmp"
            }

            val binder = FreshIdentifier(name, true).setType(prefix.getType) // Is it full of women though?

            // prefix becomes binder
            substMap += prefix -> Variable(binder)
            substMap += CaseClassInstanceOf(cd, prefix) -> BooleanLiteral(true)

            val subconds = for (id <- cd.fieldsIds) yield {
              val fieldSel = CaseClassSelector(cd, prefix, id)
              if (conditions contains fieldSel) {
                computePatternFor(conditions(fieldSel), fieldSel)
              } else {
                val b = FreshIdentifier(id.name, true).setType(id.getType)
                substMap += fieldSel -> Variable(b)
                WildcardPattern(Some(b))
              }
            }

            CaseClassPattern(Some(binder), cd, subconds)
          }

          val (scrutinees, patterns) = scrutSet.toSeq.map(s => (s, computePatternFor(conditions(s), s))).unzip

          val (scrutinee, pattern) = if (scrutinees.size > 1) {
            (Tuple(scrutinees), TuplePattern(None, patterns))
          } else {
            (scrutinees.head, patterns.head)
          }

          // We use searchAndReplace to replace the biggest match first
          // (topdown).
          // So replaceing using Map(a => b, CC(a) => d) will replace
          // "CC(a)" by "d" and not by "CC(b)"
          val newThen = preMap(substMap.lift)(thenn)

          // Remove unused binders
          val vars = variablesOf(newThen)

          def simplerBinder(oid: Option[Identifier]) = oid.filter(vars(_))

          def simplifyPattern(p: Pattern): Pattern = p match {
            case CaseClassPattern(ob, cd, subpatterns) =>
              CaseClassPattern(simplerBinder(ob), cd, subpatterns map simplifyPattern)
            case WildcardPattern(ob) =>
              WildcardPattern(simplerBinder(ob))
            case TuplePattern(ob, patterns) =>
              TuplePattern(simplerBinder(ob), patterns map simplifyPattern)
            case _ =>
              p
          }

          val resCases = List(
                           SimpleCase(simplifyPattern(pattern), newThen),
                           SimpleCase(WildcardPattern(None), elze)
                         )

          def mergePattern(to: Pattern, anchor: Identifier, pat: Pattern): Pattern = to match {
            case CaseClassPattern(ob, cd, subs) =>
              if (ob == Some(anchor)) {
                sys.error("WOOOT: "+to+" <<= "+pat +" on "+anchor)
                pat
              } else {
                CaseClassPattern(ob, cd, subs.map(mergePattern(_, anchor, pat)))
              }
            case InstanceOfPattern(ob, cd) =>
              if (ob == Some(anchor)) {
                sys.error("WOOOT: "+to+" <<= "+pat +" on "+anchor)
                pat
              } else {
                InstanceOfPattern(ob, cd)
              }

            case WildcardPattern(ob) =>
              if (ob == Some(anchor)) {
                pat
              } else {
                WildcardPattern(ob)
              }
            case TuplePattern(ob,subs) =>
              if (ob == Some(anchor)) {
                sys.error("WOOOT: "+to+" <<= "+pat +" on "+anchor)
                pat
              } else {
                TuplePattern(ob, subs)
              }
          }

          val newCases = resCases.flatMap { c => c match {
            case SimpleCase(wp: WildcardPattern, m @ MatchExpr(ex, cases)) if ex == scrutinee  =>
              cases

            case SimpleCase(pattern, m @ MatchExpr(v @ Variable(id), cases)) =>
              if (pattern.binders(id)) {
                cases.map{ nc =>
                  SimpleCase(mergePattern(pattern, id, nc.pattern), nc.rhs)
                }
              } else {
                Seq(c)
              }
            case _ => Seq(c)
          }}

          var finalMatch = MatchExpr(scrutinee, List(newCases.head)).setType(e.getType)

          for (toAdd <- newCases.tail if !isMatchExhaustive(finalMatch)) {
            finalMatch = MatchExpr(scrutinee, finalMatch.cases :+ toAdd).setType(e.getType)
          }

          finalMatch

        } else {
          e
        }
      case _ =>
        e
    }

    simplePostTransform(post)(e)
  }

  /**
   * Simplify If expressions when the branch is predetermined by the path
   * condition
   */
  def simplifyTautologies(sf: SolverFactory[Solver])(expr : Expr) : Expr = {
    val solver = SimpleSolverAPI(sf)

    def pre(e : Expr) = e match {

      case LetDef(fd, expr) if fd.hasPrecondition =>
       val pre = fd.precondition.get 

        solver.solveVALID(pre) match {
          case Some(true)  =>
            fd.precondition = None

          case Some(false) => solver.solveSAT(pre) match {
            case (Some(false), _) =>
              fd.precondition = Some(BooleanLiteral(false).copiedFrom(e))
            case _ =>
          }
          case None =>
        }

        e

      case IfExpr(cond, thenn, elze) => 
        try {
          solver.solveVALID(cond) match {
            case Some(true)  => thenn
            case Some(false) => solver.solveVALID(Not(cond)) match {
              case Some(true) => elze
              case _ => e
            }
            case None => e
          }
        } catch {
          // let's give up when the solver crashes
          case _ : Exception => e 
        }

      case _ => e
    }

    simplePreTransform(pre)(expr)
  }

  def simplifyPaths(sf: SolverFactory[Solver]): Expr => Expr = {
    new SimplifierWithPaths(sf).transform _
  }

  trait Traverser[T] {
    def traverse(e: Expr): T
  }

  class ChooseCollectorWithPaths extends TransformerWithPC with Traverser[Seq[(Choose, Expr)]] {
    type C = Seq[Expr]
    val initC = Nil
    def register(e: Expr, path: C) = path :+ e

    var results: Seq[(Choose, Expr)] = Nil

    override def rec(e: Expr, path: C) = e match {
      case c : Choose =>
        results = results :+ (c, And(path))
        c
      case _ =>
        super.rec(e, path)
    }

    def traverse(e: Expr) = {
      results = Nil
      rec(e, initC)
      results
    }
  }

  /**
   * Eliminates tuples of arity 0 and 1.
   * Used to simplify synthesis solutions
   *
   * Only rewrites local fundefs.
   */
  def rewriteTuples(expr: Expr) : Expr = {
    def mapType(tt : TypeTree) : Option[TypeTree] = tt match {
      case TupleType(ts) => ts.size match {
        case 0 => Some(UnitType)
        case 1 => Some(ts(0))
        case _ =>
          val tss = ts.map(mapType)
          if(tss.exists(_.isDefined)) {
            Some(TupleType((tss zip ts).map(p => p._1.getOrElse(p._2))))
          } else {
            None
          }
      }
      case ListType(t)           => mapType(t).map(ListType(_))
      case SetType(t)            => mapType(t).map(SetType(_))
      case MultisetType(t)       => mapType(t).map(MultisetType(_))
      case ArrayType(t)          => mapType(t).map(ArrayType(_))
      case MapType(f,t)          => 
        val (f2,t2) = (mapType(f),mapType(t))
        if(f2.isDefined || t2.isDefined) {
          Some(MapType(f2.getOrElse(f), t2.getOrElse(t)))
        } else {
          None
        }
      case a : AbstractClassType => None
      case c : CaseClassType     =>
        // This is really just one big assertion. We don't rewrite class defs.
        val ccd = c.classDef
        val fieldTypes = ccd.fields.map(_.tpe)
        if(fieldTypes.exists(t => t match {
          case TupleType(ts) if ts.size <= 1 => true
          case _ => false
        })) {
          scala.sys.error("Cannot rewrite case class def that contains degenerate tuple types.")
        } else {
          None
        }
      case Untyped | AnyType | BottomType | BooleanType | Int32Type | UnitType => None  
    }

    var idMap     = Map[Identifier, Identifier]()
    var funDefMap = Map.empty[FunDef,FunDef]

    def fd2fd(funDef : FunDef) : FunDef = funDefMap.get(funDef) match {
      case Some(fd) => fd
      case None =>
        if(funDef.args.map(vd => mapType(vd.tpe)).exists(_.isDefined)) {
          scala.sys.error("Cannot rewrite function def that takes degenerate tuple arguments,")
        }
        val newFD = mapType(funDef.returnType) match {
          case None => funDef
          case Some(rt) =>
            val fd = new FunDef(FreshIdentifier(funDef.id.name, true), rt, funDef.args)
            // These will be taken care of in the recursive traversal.
            fd.body = funDef.body
            fd.precondition = funDef.precondition
            funDef.postcondition match {
              case Some((id, post)) =>
                val freshId = FreshIdentifier(id.name, true).setType(rt)
                idMap += id -> freshId
                fd.postcondition = Some((freshId, post))
              case None =>
                fd.postcondition = None
            }
            fd
        }
        funDefMap = funDefMap.updated(funDef, newFD)
        newFD
    }

    def pre(e : Expr) : Expr = e match {
      case Tuple(Seq()) => UnitLiteral
      case Variable(id) if idMap contains id => Variable(idMap(id))

      case Tuple(Seq(s)) => pre(s)

      case ts @ TupleSelect(t, 1) => t.getType match {
        case TupleOneType(_) => pre(t)
        case _ => ts
      }

      case LetTuple(bs, v, bdy) if bs.size == 1 =>
        Let(bs(0), v, bdy)

      case l @ LetDef(fd, bdy) =>
        LetDef(fd2fd(fd), bdy)

      case FunctionInvocation(fd, args) =>
        FunctionInvocation(fd2fd(fd), args)

      case _ => e
    }

    simplePreTransform(pre)(expr)
  }

  def formulaSize(e: Expr): Int = e match {
    case t: Terminal =>
      1

    case UnaryOperator(e, builder) =>
      formulaSize(e)+1

    case BinaryOperator(e1, e2, builder) =>
      formulaSize(e1)+formulaSize(e2)+1

    case NAryOperator(es, _) =>
      es.map(formulaSize).foldRight(0)(_ + _)+1
  }

  def collectChooses(e: Expr): List[Choose] = {
    new ChooseCollectorWithPaths().traverse(e).map(_._1).toList
  }

  def containsChoose(e: Expr): Boolean = {
    simplePreTransform{
      case Choose(_, _) => return true
      case e => e
    }(e)
    false
  }

  /**
   * Returns the value for an identifier given a model.
   */
  def valuateWithModel(model: Map[Identifier, Expr])(id: Identifier): Expr = {
    model.getOrElse(id, simplestValue(id.getType))
  }

  /**
   * Substitute (free) variables in an expression with values form a model.
   * 
   * Complete with simplest values in case of incomplete model.
   */
  def valuateWithModelIn(expr: Expr, vars: Set[Identifier], model: Map[Identifier, Expr]): Expr = {
    val valuator = valuateWithModel(model) _
    replace(vars.map(id => Variable(id) -> valuator(id)).toMap, expr)
  }

  /**
   * Simple, local simplification on arithmetic
   *
   * You should not assume anything smarter than some constant folding and
   * simple cancelation. To avoid infinite cycle we only apply simplification
   * that reduce the size of the tree. The only guarentee from this function is
   * to not augment the size of the expression and to be sound.
   */
  def simplifyArithmetic(expr: Expr): Expr = {
    def simplify0(expr: Expr): Expr = (expr match {
      case Plus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 + i2)
      case Plus(IntLiteral(0), e) => e
      case Plus(e, IntLiteral(0)) => e
      case Plus(e1, UMinus(e2)) => Minus(e1, e2)
      case Plus(Plus(e, IntLiteral(i1)), IntLiteral(i2)) => Plus(e, IntLiteral(i1+i2))
      case Plus(Plus(IntLiteral(i1), e), IntLiteral(i2)) => Plus(IntLiteral(i1+i2), e)

      case Minus(e, IntLiteral(0)) => e
      case Minus(IntLiteral(0), e) => UMinus(e)
      case Minus(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 - i2)
      case Minus(e1, UMinus(e2)) => Plus(e1, e2)
      case Minus(e1, Minus(UMinus(e2), e3)) => Plus(e1, Plus(e2, e3))

      case UMinus(IntLiteral(x)) => IntLiteral(-x)
      case UMinus(UMinus(x)) => x
      case UMinus(Plus(UMinus(e1), e2)) => Plus(e1, UMinus(e2))
      case UMinus(Minus(e1, e2)) => Minus(e2, e1)

      case Times(IntLiteral(i1), IntLiteral(i2)) => IntLiteral(i1 * i2)
      case Times(IntLiteral(1), e) => e
      case Times(IntLiteral(-1), e) => UMinus(e)
      case Times(e, IntLiteral(1)) => e
      case Times(IntLiteral(0), _) => IntLiteral(0)
      case Times(_, IntLiteral(0)) => IntLiteral(0)
      case Times(IntLiteral(i1), Times(IntLiteral(i2), t)) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i1), Times(t, IntLiteral(i2))) => Times(IntLiteral(i1*i2), t)
      case Times(IntLiteral(i), UMinus(e)) => Times(IntLiteral(-i), e)
      case Times(UMinus(e), IntLiteral(i)) => Times(e, IntLiteral(-i))
      case Times(IntLiteral(i1), Division(e, IntLiteral(i2))) if i2 != 0 && i1 % i2 == 0 => Times(IntLiteral(i1/i2), e)

      case Division(IntLiteral(i1), IntLiteral(i2)) if i2 != 0 => IntLiteral(i1 / i2)
      case Division(e, IntLiteral(1)) => e

      //here we put more expensive rules
      //btw, I know those are not the most general rules, but they lead to good optimizations :)
      case Plus(UMinus(Plus(e1, e2)), e3) if e1 == e3 => UMinus(e2)
      case Plus(UMinus(Plus(e1, e2)), e3) if e2 == e3 => UMinus(e1)
      case Minus(e1, e2) if e1 == e2 => IntLiteral(0) 
      case Minus(Plus(e1, e2), Plus(e3, e4)) if e1 == e4 && e2 == e3 => IntLiteral(0)
      case Minus(Plus(e1, e2), Plus(Plus(e3, e4), e5)) if e1 == e4 && e2 == e3 => UMinus(e5)

      //default
      case e => e
    }).copiedFrom(expr)

    def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
    }

    fix(simplePostTransform(simplify0))(expr)
  }

  /**
   * Checks whether a predicate is inductive on a certain identfier.
   *
   * isInductive(foo(a, b), a) where a: List will check whether
   *    foo(Nil, b) and
   *    foo(Cons(h,t), b) => foo(t, b)
   */
  def isInductiveOn(sf: SolverFactory[Solver])(expr: Expr, on: Identifier): Boolean = on match {
    case IsTyped(origId, AbstractClassType(cd)) =>
      def isAlternativeRecursive(cd: CaseClassDef): Boolean = {
        cd.fieldsIds.exists(_.getType == origId.getType)
      }

      val toCheck = cd.knownDescendents.collect {
        case ccd: CaseClassDef =>
          val isType = CaseClassInstanceOf(ccd, Variable(on))

            val recSelectors = ccd.fieldsIds.filter(_.getType == on.getType)

            if (recSelectors.isEmpty) {
              Seq()
            } else {
              val v = Variable(on)

              recSelectors.map{ s =>
                And(And(isType, expr), Not(replace(Map(v -> CaseClassSelector(ccd, v, s)), expr)))
              }
            }
      }.flatten

      val solver = SimpleSolverAPI(sf)

      toCheck.forall { cond =>
        solver.solveSAT(cond) match {
            case (Some(false), _)  =>
              true
            case (Some(true), model)  =>
              false
            case (None, _)  =>
              // Should we be optimistic here?
              false
        }
      }
    case _ =>
      false
  }

  /**
   * Checks whether two trees are homomoprhic modulo an identifier map.
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
      i1 == i2 || map.get(i1).map(_ == i2).getOrElse(false)
    }

    def fdHomo(fd1: FunDef, fd2: FunDef)(implicit map: Map[Identifier, Identifier]) = {
      if (fd1.args.size == fd2.args.size &&
          fd1.precondition.size == fd2.precondition.size &&
          fd1.body.size == fd2.body.size &&
          fd1.postcondition.size == fd2.postcondition.size) {

        val newMap = map +
                     (fd1.id -> fd2.id) ++
                     (fd1.args zip fd2.args).map{ case (vd1, vd2) => (vd1.id, vd2.id) }

        val preMatch = (fd1.precondition zip fd2.precondition).forall {
          case (e1, e2) => isHomo(e1, e2)(newMap)
        }

        val postMatch = (fd1.postcondition zip fd2.postcondition).forall {
          case ((id1, e1), (id2, e2)) => isHomo(e1, e2)(newMap + (id1 -> id2))
        }

        val bodyMatch = (fd1.body zip fd2.body).forall {
          case (e1, e2) => isHomo(e1, e2)(newMap)
        }

        preMatch && postMatch && bodyMatch
      } else {
        false

      }
    }

    def isHomo(t1: Expr, t2: Expr)(implicit map: Map[Identifier,Identifier]): Boolean = {
      val res = (t1, t2) match {
        case (Variable(i1), Variable(i2)) =>
          idHomo(i1, i2)

        case (Choose(ids1, e1), Choose(ids2, e2)) =>
          isHomo(e1, e2)(map ++ (ids1 zip ids2))

        case (Let(id1, v1, e1), Let(id2, v2, e2)) =>
          isHomo(v1, v2) &&
          isHomo(e1, e2)(map + (id1 -> id2))

        case (LetTuple(ids1, v1, e1), LetTuple(ids2, v2, e2)) =>
          if (ids1.size == ids2.size) {
            isHomo(v1, v2) &&
            isHomo(e1, e2)(map ++ (ids1 zip ids2))
          } else {
            false
          }

        case (LetDef(fd1, e1), LetDef(fd2, e2)) =>
          fdHomo(fd1, fd2) &&
          isHomo(e1, e2)(map + (fd1.id -> fd2.id))

        case (MatchExpr(s1, cs1), MatchExpr(s2, cs2)) =>
          if (cs1.size == cs2.size) {
            val scrutMatch = isHomo(s1, s2)

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

              case (TuplePattern(ob1, subs1), TuplePattern(ob2, subs2)) =>
                val m = Map[Identifier, Identifier]() ++ (ob1 zip ob2)

                if (ob1.size == ob2.size && subs1.size == subs2.size) {
                  (subs1 zip subs2).map { case (p1, p2) => patternHomo(p1, p2) }.foldLeft((true, m)) {
                    case ((b1, m1), (b2,m2)) => (b1 && b2, m1 ++ m2)
                  }
                } else {
                  (false, Map())
                }
              case _ =>
                (false, Map())
            }

            val casesMatch = (cs1 zip cs2).forall {
              case (SimpleCase(p1, e1), SimpleCase(p2, e2)) =>
                val (h, nm) = patternHomo(p1, p2)

                h && isHomo(e1, e2)(map ++ nm)

              case (GuardedCase(p1, g1, e1), GuardedCase(p2, g2, e2)) =>
                val (h, nm) = patternHomo(p1, p2)

                h && isHomo(g1, g2)(map ++ nm) && isHomo(e1, e2)(map ++ nm)

              case _ =>
                false
            }

            scrutMatch && casesMatch
          } else {
            false
          }

        case (FunctionInvocation(fd1, args1), FunctionInvocation(fd2, args2)) =>
          fdHomo(fd1, fd2) &&
          (args1 zip args2).forall{ case (a1, a2) => isHomo(a1, a2) }

        case Same(UnaryOperator(e1, _), UnaryOperator(e2, _)) =>
          isHomo(e1, e2)

        case Same(BinaryOperator(e11, e12, _), BinaryOperator(e21, e22, _)) =>
          isHomo(e11, e21) && isHomo(e12, e22)

        case Same(NAryOperator(es1, _), NAryOperator(es2, _)) =>
          if (es1.size == es2.size) {
            (es1 zip es2).forall{ case (e1, e2) => isHomo(e1, e2) }
          } else {
            false
          }
        case Same(t1 : Terminal, t2: Terminal) =>
          true

        case _ =>
          false
      }

      res
    }

    isHomo(t1,t2)
  }

  /**
   * Checks whether the match cases cover all possible inputs
   * Used when reconstructing pattern matching from ITE.
   *
   * e.g. The following:
   *
   * list match {
   *   case Cons(_, Cons(_, a)) =>
   *
   *   case Cons(_, Nil) =>
   *
   *   case Nil =>
   *
   * }
   *
   * is exaustive.
   */
  def isMatchExhaustive(m: MatchExpr): Boolean = {
    /**
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
     */ 
    def areExaustive(pss: Seq[(TypeTree, Seq[Pattern])]): Boolean = pss.forall { case (tpe, ps) =>

      tpe match {
        case TupleType(tpes) =>
          val subs = ps.collect {
            case TuplePattern(_, bs) =>
              bs
          }

          areExaustive(tpes zip subs.transpose)

        case _: ClassType =>

          def typesOf(tpe: TypeTree): Set[CaseClassDef] = tpe match {
            case AbstractClassType(ctp) =>
              ctp.knownDescendents.collect { case c: CaseClassDef => c }.toSet

            case CaseClassType(ctd) =>
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
              subChecks --= typesOf(classDefToClassType(cct))

            case CaseClassPattern(_, ccd, subs) =>
              // We record the patterns per types, if they still need to be checked
              if (subChecks contains ccd) {
                subChecks += (ccd -> (subChecks(ccd) :+ subs))
              }

            case _ =>
              sys.error("Unnexpected case: "+p)
          }

          subChecks.forall { case (ccd, subs) =>
            val tpes = ccd.fields.map(_.tpe)

            if (subs.isEmpty) {
              false
            } else {
              areExaustive(tpes zip subs.transpose)
            }
          }

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

    areExaustive(Seq((m.scrutinee.getType, patterns)))
  }

  /**
   * Flattens a function that contains a LetDef with a direct call to it
   * Used for merging synthesis results.
   *
   * def foo(a, b) {
   *   def bar(c, d) {
   *      if (..) { bar(c, d) } else { .. }
   *   }
   *   bar(b, a)
   * }
   * 
   * becomes
   * 
   * def foo(a, b) {
   *   if (..) { foo(b, a) } else { .. }
   * }
   **/
  def flattenFunctions(fdOuter: FunDef): FunDef = {
    fdOuter.body match {
      case Some(LetDef(fdInner, FunctionInvocation(fdInner2, args))) if fdInner == fdInner2 =>
        val argsDef  = fdOuter.args.map(_.id)
        val argsCall = args.collect { case Variable(id) => id }

        if (argsDef.toSet == argsCall.toSet) {
          val defMap = argsDef.zipWithIndex.toMap
          val rewriteMap = argsCall.map(defMap)

          val innerIdsToOuterIds = (fdInner.args.map(_.id) zip argsCall).toMap

          def pre(e: Expr) = e match {
            case FunctionInvocation(fd, args) if fd == fdInner =>
              val newArgs = (args zip rewriteMap).sortBy(_._2)
              FunctionInvocation(fdOuter, newArgs.map(_._1))
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
              Some(And(oe, simplePreTransform(pre)(ie)))
          }

          def mergePost(outer: Option[(Identifier, Expr)], inner: Option[(Identifier, Expr)]): Option[(Identifier, Expr)] = (outer, inner) match {
            case (None, Some((iid, ie))) =>
              Some((iid, simplePreTransform(pre)(ie)))
            case (Some(oe), None) =>
              Some(oe)
            case (None, None) =>
              None
            case (Some((oid, oe)), Some((iid, ie))) =>
              Some((oid, And(oe, replaceFromIDs(Map(iid -> Variable(oid)), simplePreTransform(pre)(ie)))))
          }

          val newFd = fdOuter.duplicate

          newFd.body          = fdInner.body.map(b => simplePreTransform(pre)(b))
          newFd.precondition  = mergePre(fdOuter.precondition, fdInner.precondition)
          newFd.postcondition = mergePost(fdOuter.postcondition, fdInner.postcondition)

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
      coefs.toList.zip(IntLiteral(1) :: freeVars.toList.map(Variable(_))).foldLeft[Expr](IntLiteral(0))((acc, t) => {
        if(t._1 == IntLiteral(0)) acc else Plus(acc, Times(t._1, t._2))
      })
    } catch {
      case _: Throwable =>
        expr
    }
    simplifyArithmetic(expr0)
  }


  /**
   * Deprecated API
   * ========
   */

  @deprecated("Use postMap instead", "Leon 0.2.0")
  def searchAndReplace(f: Expr => Option[Expr])(e: Expr) = postMap(f)(e)


}
