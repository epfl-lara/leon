/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Constructors._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common.Identifier
import purescala.Definitions.{TypedFunDef, Program}
import purescala.Expressions._

import leon.solvers.SolverFactory
import leon.utils.StreamUtils.cartesianProduct

class NDEvaluator(ctx: LeonContext, prog: Program)
  extends ContextualEvaluator(ctx, prog, 50000)
  with DefaultContexts
{

  val name = "ND-evaluator"
  val description = "Non-deterministic interpreter for Leon programs that returns a Stream of solutions"

  type Value = Stream[Expr]

  case class NDValue(tp: TypeTree) extends Expr with Terminal {
    val getType = tp
  }

  protected[evaluators] def e(expr: Expr)(implicit rctx: RC, gctx: GC): Stream[Expr] = expr match {
    case Variable(id) =>
      rctx.mappings.get(id).toStream

    case Application(caller, args) =>
      for {
        cl <- e(caller).distinct
        newArgs <- cartesianProduct(args map e).distinct
        res <- cl match {
          case l @ Lambda(params, body) =>
            val mapping = l.paramSubst(newArgs)
            e(body)(rctx.withNewVars(mapping), gctx).distinct
          case PartialLambda(mapping, _) =>
            mapping.collectFirst {
              case (pargs, res) if (newArgs zip pargs).forall { case (f, r) => f == r } =>
                res
            }.toStream
          case _ =>
            Stream()
        }
      } yield res

    case Let(i,v,b) =>
      for {
        ev <- e(v).distinct
        eb <- e(b)(rctx.withNewVar(i, ev), gctx).distinct
      } yield eb

    case Assert(cond, oerr, body) =>
      e(IfExpr(Not(cond), Error(expr.getType, oerr.getOrElse("Assertion failed @"+expr.getPos)), body))

    case en@Ensuring(body, post) =>
      if ( exists{
        case Hole(_,_) => true
        case WithOracle(_,_) => true
        case _ => false
      }(en)) {
        import synthesis.ConversionPhase.convert
        e(convert(en, ctx))
      } else {
        e(en.toAssert)
      }

    case Error(tpe, desc) =>
      Stream()

    case NDValue(tp) =>
      import grammars.ValueGrammar
      ValueGrammar.getProductions(tp).toStream.map{ g => g.builder(Seq())}

    case IfExpr(cond, thenn, elze) =>
      e(cond).distinct.flatMap {
        case BooleanLiteral(true) => e(thenn)
        case BooleanLiteral(false) => e(elze)
        case other => Stream()
      }.distinct

    case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq(set)) if fd == program.library.setToList.get =>
      val cons = program.library.Cons.get
      val nil = CaseClass(CaseClassType(program.library.Nil.get, Seq(tp)), Seq())
      def mkCons(h: Expr, t: Expr) = CaseClass(CaseClassType(cons, Seq(tp)), Seq(h,t))
      e(set).distinct.collect {
        case FiniteSet(els, _) =>
          els.foldRight(nil)(mkCons)
      }.distinct

    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        return Stream()
      }
      gctx.stepsLeft -= 1

      for {
        evArgs               <- cartesianProduct(args map e).distinct
        // build a mapping for the function...
        frame = rctx.withNewVars(tfd.paramSubst(evArgs))
        BooleanLiteral(true) <- e(tfd.precOrTrue)(frame, gctx).distinct
        body                 <- tfd.body.orElse(rctx.mappings.get(tfd.id)).toStream
        callResult           <- e(body)(frame, gctx).distinct
        BooleanLiteral(true) <- e(application(tfd.postOrTrue, Seq(callResult)))(frame, gctx).distinct
      } yield callResult

    case And(args) if args.isEmpty =>
      Stream(BooleanLiteral(true))
    case And(args) =>
      e(args.head).distinct.flatMap {
        case BooleanLiteral(false) => Stream(BooleanLiteral(false))
        case BooleanLiteral(true) => e(andJoin(args.tail))
        case other => Stream()
      }

    case Or(args) if args.isEmpty =>
      Stream(BooleanLiteral(false))
    case Or(args) =>
      e(args.head).distinct.flatMap {
        case BooleanLiteral(true) => Stream(BooleanLiteral(true))
        case BooleanLiteral(false) => e(orJoin(args.tail))
        case other => Stream()
      }

    case Implies(lhs, rhs) =>
      e(Or(Not(lhs), rhs))

    case l @ Lambda(_, _) =>
      val (nl, structSubst) = normalizeStructure(l)
      val mapping = variablesOf(l).map(id =>
        structSubst(id) -> (e(Variable(id)) match {
          case Stream(v) => v
          case _ => return Stream()
        })
      ).toMap
      Stream(replaceFromIDs(mapping, nl))

    case PartialLambda(mapping, tpe) =>
      def solveOne(pair: (Seq[Expr], Expr)) = {
        val (args, res) = pair
        for {
          as <- cartesianProduct(args map e)
          r  <- e(res)
        } yield as -> r
      }
      cartesianProduct(mapping map solveOne) map (PartialLambda(_, tpe))

    case f @ Forall(fargs, TopLevelAnds(conjuncts)) =>

      def solveOne(conj: Expr) = {
        val instantiations = try {
          forallInstantiations(gctx, fargs, conj)
        } catch {
          case _: EvalError => Seq()
        }
        for {
          es <- cartesianProduct(instantiations.map { case (enabler, mapping) =>
            e(Implies(enabler, conj))(rctx.withNewVars(mapping), gctx)
          })
          res <- e(andJoin(es))
        } yield res
      }

      for {
        conj <- cartesianProduct(conjuncts map solveOne)
        res <- e(andJoin(conj))
      } yield res

    case p : Passes =>
      e(p.asConstraint)

    case choose: Choose =>

      // TODO add memoization
      implicit val debugSection = utils.DebugSectionSynthesis

      val p = synthesis.Problem.fromSpec(choose.pred)

      ctx.reporter.debug("Executing choose!")

      val tStart = System.currentTimeMillis

      val solverf = SolverFactory.getFromSettings(ctx, program)
      val solver  = solverf.getNewSolver()

      try {
        val eqs = p.as.map {
          case id =>
            Equals(Variable(id), rctx.mappings(id))
        }

        val cnstr = andJoin(eqs ::: p.pc :: p.phi :: Nil)
        solver.assertCnstr(cnstr)

        def getSolution = solver.check match {
          case Some(true) =>
            val model = solver.getModel

            val valModel = valuateWithModel(model) _

            val res = p.xs.map(valModel)
            val leonRes = tupleWrap(res)
            val total = System.currentTimeMillis-tStart

            ctx.reporter.debug("Synthesis took "+total+"ms")
            ctx.reporter.debug("Finished synthesis with "+leonRes.asString)

            Some(leonRes)
          case _ =>
            None
        }

        Stream.iterate(getSolution)(prev => {
          val ensureDistinct = Not(Equals(p.xs.head.toVariable, prev.get))
          solver.assertCnstr(ensureDistinct)
          getSolution
        }).takeWhile(_.isDefined).map(_.get)

      } catch {
        case e: Throwable =>
          Stream()
      } finally {
        solverf.reclaim(solver)
        solverf.shutdown()
      }


    case MatchExpr(scrut, cases) =>

      def matchesCase(scrut: Expr, caze: MatchCase)(implicit rctx: RC, gctx: GC): Stream[(MatchCase, Map[Identifier, Expr])] = {
        import purescala.TypeOps.isSubtypeOf

        def matchesPattern(pat: Pattern, expr: Expr): Stream[Map[Identifier, Expr]] = (pat, expr) match {
          case (InstanceOfPattern(ob, pct), e) =>
            (if (isSubtypeOf(e.getType, pct)) {
              Some(obind(ob, e))
            } else {
              None
            }).toStream
          case (WildcardPattern(ob), e) =>
            Stream(obind(ob, e))

          case (CaseClassPattern(ob, pct, subs), CaseClass(ct, args)) =>
            if (pct == ct) {
              val subMaps = (subs zip args).map{ case (s, a) => matchesPattern(s, a) }
              cartesianProduct(subMaps).map( _.flatten.toMap ++ obind(ob, expr))
            } else {
              Stream()
            }
          case (up @ UnapplyPattern(ob, _, subs), scrut) =>
            e(FunctionInvocation(up.unapplyFun, Seq(scrut))) flatMap {
              case CaseClass(CaseClassType(cd, _), Seq()) if cd == program.library.Nil.get =>
                None
              case CaseClass(CaseClassType(cd, _), Seq(arg)) if cd == program.library.Cons.get =>
                val subMaps = subs zip unwrapTuple(arg, up.unapplyFun.returnType.isInstanceOf[TupleType]) map {
                  case (s,a) => matchesPattern(s,a)
                }
                cartesianProduct(subMaps).map( _.flatten.toMap ++ obind(ob, expr))
              case other =>
                None
            }
          case (TuplePattern(ob, subs), Tuple(args)) =>
            if (subs.size == args.size) {
              val subMaps = (subs zip args).map { case (s, a) => matchesPattern(s, a) }
              cartesianProduct(subMaps).map(_.flatten.toMap ++ obind(ob, expr))
            } else Stream()
          case (LiteralPattern(ob, l1) , l2 : Literal[_]) if l1 == l2 =>
            Stream(obind(ob,l1))
          case _ => Stream()
        }

        def obind(ob: Option[Identifier], e: Expr): Map[Identifier, Expr] = {
          Map[Identifier, Expr]() ++ ob.map(id => id -> e)
        }

        caze match {
          case SimpleCase(p, rhs) =>
            matchesPattern(p, scrut).map(r =>
              (caze, r)
            )

          case GuardedCase(p, g, rhs) =>
            for {
              r <- matchesPattern(p, scrut)
              BooleanLiteral(true) <- e(g)(rctx.withNewVars(r), gctx)
            } yield (caze, r)
        }
      }

      for {
        rscrut  <- e(scrut)
        cs      <- cases.toStream.map(c => matchesCase(rscrut, c)).find(_.nonEmpty).toStream
        (c, mp) <- cs
        res     <- e(c.rhs)(rctx.withNewVars(mp), gctx)
      } yield res

    case Operator(es, _) =>
      cartesianProduct(es map e) flatMap { es =>
        try {
          Some(step(expr, es))
        } catch {
          case _: EvalError | _: RuntimeError =>
            None
        }
      }

    case other =>
      context.reporter.error(other.getPos, "Error: don't know how to handle " + other.asString + " in Evaluator ("+other.getClass+").")
      Stream()
  }


  protected def step(expr: Expr, subs: Seq[Expr])(implicit rctx: RC, gctx: GC): Expr = (expr, subs) match {
    case (Tuple(_), ts) =>
      Tuple(ts)

    case (TupleSelect(_, i), rs) =>
      rs(i - 1)

    case (Assert(_, oerr, _), Seq(BooleanLiteral(cond), body)) =>
      if (cond) body
      else throw RuntimeError(oerr.getOrElse("Assertion failed @" + expr.getPos))

    case (Error(_, desc), _) =>
      throw RuntimeError("Error reached in evaluation: " + desc)

    case (FunctionInvocation(TypedFunDef(fd, Seq(tp)), _), Seq(FiniteSet(els, _))) if fd == program.library.setToList.get =>
      val cons = program.library.Cons.get
      val nil = CaseClass(CaseClassType(program.library.Nil.get, Seq(tp)), Seq())
      def mkCons(h: Expr, t: Expr) = CaseClass(CaseClassType(cons, Seq(tp)), Seq(h, t))
      els.foldRight(nil)(mkCons)

    case (Not(_), Seq(BooleanLiteral(arg))) =>
      BooleanLiteral(!arg)

    case (Implies(_, _) Seq (BooleanLiteral(b1), BooleanLiteral(b2))) =>
      BooleanLiteral(!b1 || b2)

    case (Equals(_, _), Seq(lv, rv)) =>
      (lv, rv) match {
        case (FiniteSet(el1, _), FiniteSet(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteMap(el1, _, _), FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (PartialLambda(m1, _), PartialLambda(m2, _)) => BooleanLiteral(m1.toSet == m2.toSet)
        case _ => BooleanLiteral(lv == rv)
      }

    case (CaseClass(cd, _), args) =>
      CaseClass(cd, args)

    case (AsInstanceOf(_, ct), Seq(ce)) =>
      if (isSubtypeOf(ce.getType, ct)) {
        ce
      } else {
        throw RuntimeError("Cast error: cannot cast " + ce.asString + " to " + ct.asString)
      }

    case (IsInstanceOf(_, ct), Seq(ce)) =>
      BooleanLiteral(isSubtypeOf(ce.getType, ct))

    case (CaseClassSelector(ct1, _, sel), Seq(CaseClass(ct2, args))) if ct1 == ct2 =>
      args(ct1.classDef.selectorID2Index(sel))

    case (Plus(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      InfiniteIntegerLiteral(i1 + i2)

    case (Minus(_, _) Seq (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      InfiniteIntegerLiteral(i1 - i2)

    case (Times(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      InfiniteIntegerLiteral(i1 * i2)

    case (Division(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      if (i2 != BigInt(0)) InfiniteIntegerLiteral(i1 / i2)
      else throw RuntimeError("Division by 0.")

    case (Remainder(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      if (i2 != BigInt(0)) InfiniteIntegerLiteral(i1 % i2)
      else throw RuntimeError("Remainder of division by 0.")

    case (Modulo(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
      if (i2 < 0)
        InfiniteIntegerLiteral(i1 mod (-i2))
      else if (i2 != BigInt(0))
        InfiniteIntegerLiteral(i1 mod i2)
      else
        throw RuntimeError("Modulo of division by 0.")

    case (RealPlus(_, _), Seq(FractionalLiteral(ln, ld), FractionalLiteral(rn, rd))) =>
      normalizeFraction(FractionalLiteral(ln * rd + rn * ld, ld * rd))

    case (RealMinus(_, _), Seq(FractionalLiteral(ln, ld), FractionalLiteral(rn, rd))) =>
      normalizeFraction(FractionalLiteral(ln * rd - rn * ld, ld * rd))

    case (RealTimes(_, _), Seq(FractionalLiteral(ln, ld), FractionalLiteral(rn, rd))) =>
      normalizeFraction(FractionalLiteral(ln * rn, ld * rd))

    case (RealDivision(_, _), Seq(FractionalLiteral(ln, ld), FractionalLiteral(rn, rd))) =>
      if (rn != 0) normalizeFraction(FractionalLiteral(ln * rd, ld * rn))
      else throw RuntimeError("Division by 0.")

    case (BVPlus(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 + i2)

    case (BVMinus(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 - i2)

    case (UMinus(_), Seq(InfiniteIntegerLiteral(i))) =>
      InfiniteIntegerLiteral(-i)

    case (BVUMinus(_), Seq(IntLiteral(i))) =>
      IntLiteral(-i)

    case (RealUMinus(_), Seq(FractionalLiteral(n, d))) =>
      FractionalLiteral(-n, d)

    case (BVNot(_), Seq(IntLiteral(i))) =>
      IntLiteral(~i)

    case (BVTimes(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 * i2)

    case (BVDivision(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      if (i2 != 0) IntLiteral(i1 / i2)
      else throw RuntimeError("Division by 0.")

    case (BVRemainder(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      if (i2 != 0) IntLiteral(i1 % i2)
      else throw RuntimeError("Remainder of division by 0.")

    case (BVAnd(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 & i2)

    case (BVOr(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 | i2)

    case (BVXOr(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 ^ i2)

    case (BVShiftLeft(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 << i2)

    case (BVAShiftRight(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 >> i2)

    case (BVLShiftRight(_, _), Seq(IntLiteral(i1), IntLiteral(i2))) =>
      IntLiteral(i1 >>> i2)

    case (LessThan(_, _), Seq(el, er)) =>
      (el, er) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 < i2)
        case (a@FractionalLiteral(_, _), b@FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b)).head
          BooleanLiteral(n < 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 < c2)
        case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case (GreaterThan(_, _), Seq(el, er)) =>
      (el, er) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 > i2)
        case (a@FractionalLiteral(_, _), b@FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b)).head
          BooleanLiteral(n > 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 > c2)
        case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case (LessEquals(_, _), Seq(el, er)) =>
      (el, er) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 <= i2)
        case (a@FractionalLiteral(_, _), b@FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b)).head
          BooleanLiteral(n <= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 <= c2)
        case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case (GreaterEquals(_, _), Seq(el, er)) =>
      (el, er) match {
        case (IntLiteral(i1), IntLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => BooleanLiteral(i1 >= i2)
        case (a@FractionalLiteral(_, _), b@FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b)).head
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case (IsTyped(su@SetUnion(s1, s2), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(FiniteSet(els2, _), SetType(tpe2))
    )) =>
      FiniteSet(
        els1 ++ els2,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(su, tpe)))
      )

    case (IsTyped(su@SetIntersection(s1, s2), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(FiniteSet(els2, _), SetType(tpe2))
    )) =>
      FiniteSet(
        els1 & els2,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(su, tpe)))
      )

    case (IsTyped(su@SetDifference(s1, s2), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(FiniteSet(els2, _), SetType(tpe2))
    )) =>
      FiniteSet(
        els1 -- els2,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(su, tpe)))
      )

    case (ElementOfSet(_, _), Seq(e, FiniteSet(els, _))) =>
      BooleanLiteral(els.contains(e))

    case (SubsetOf(_, _), Seq(FiniteSet(els1, _), FiniteSet(els2, _))) =>
      BooleanLiteral(els1.subsetOf(els2))

    case (SetCardinality(_), Seq(FiniteSet(els, _))) =>
      IntLiteral(els.size)

    case (FiniteSet(_, base), els) =>
      FiniteSet(els.toSet, base)

    case (ArrayLength(_), Seq(FiniteArray(_, _, IntLiteral(length)))) =>
      IntLiteral(length)

    case (ArrayUpdated(_, _, _), Seq(
      IsTyped(FiniteArray(elems, default, length), ArrayType(tp)),
      IntLiteral(i),
      v
    )) =>
      finiteArray(elems.updated(i, v), default map {(_, length)}, tp)

    case (ArraySelect(_, _), Seq(fa@FiniteArray(elems, default, IntLiteral(length)), IntLiteral(index))) =>
      elems
        .get(index)
        .orElse(if (index >= 0 && index < length) default else None)
        .getOrElse(throw RuntimeError(s"Array out of bounds error during evaluation:\n array = $fa, index = $index"))

    case (fa@FiniteArray(_, _, _), subs) =>
      val Operator(_, builder) = fa
      builder(subs)

    case (fm@FiniteMap(_, _, _), subs) =>
      val Operator(_, builder) = fm
      builder(subs)

    case (g@MapApply(_, _), Seq(FiniteMap(m, _, _), k)) =>
      m.getOrElse(k, throw RuntimeError("Key not found: " + k.asString))

    case (u@IsTyped(MapUnion(_, _), MapType(kT, vT)), Seq(FiniteMap(m1, _, _), FiniteMap(m2, _, _))) =>
      FiniteMap(m1 ++ m2, kT, vT)

    case (i@MapIsDefinedAt(_, _), Seq(FiniteMap(elems, _, _), k)) =>
      BooleanLiteral(elems.contains(k))

    case (gv: GenericValue, Seq()) =>
      gv

    case (fl: FractionalLiteral, Seq()) =>
      normalizeFraction(fl)

    case (l: Literal[_], Seq()) =>
      l

    case (other, _) =>
      throw EvalError("Unhandled case in Evaluator: " + other.asString)

  }


}

