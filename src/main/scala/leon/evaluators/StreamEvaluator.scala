/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import purescala.Constructors._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.TypeOps.{leastUpperBound, isSubtypeOf}
import purescala.Types._
import purescala.Common.Identifier
import purescala.Definitions.{TypedFunDef, Program}
import purescala.Expressions._
import purescala.Quantification._

import leon.solvers.{SolverFactory, PartialModel}
import leon.solvers.unrolling.UnrollingProcedure
import leon.utils.StreamUtils._

import scala.concurrent.duration._

class StreamEvaluator(ctx: LeonContext, prog: Program)
  extends ContextualEvaluator(ctx, prog, 50000)
  with NDEvaluator
  with HasDefaultGlobalContext
  with HasDefaultRecContext
{

  val name = "ND-evaluator"
  val description = "Non-deterministic interpreter for Leon programs that returns a Stream of solutions"

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
          case FiniteLambda(mapping, dflt, _) =>
            // FIXME
            Stream(mapping.collectFirst {
              case (pargs, res) if (newArgs zip pargs).forall { case (f, r) => f == r } =>
                res
            }.getOrElse(dflt))
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
      e(en.toAssert)

    case Error(tpe, desc) =>
      Stream()

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
      val mapping = variablesOf(l).map(id =>
        id -> (e(Variable(id)) match {
          case Stream(v) => v
          case _ => return Stream()
        })
      ).toMap
      Stream(replaceFromIDs(mapping, l))

    case fl @ FiniteLambda(mapping, dflt, tpe) =>
      // finite lambda should always be ground!
      Stream(fl)

    case f @ Forall(fargs, body) =>

      // TODO add memoization
      implicit val debugSection = utils.DebugSectionVerification

      ctx.reporter.debug("Executing forall!")

      val mapping = variablesOf(f).map(id => id -> rctx.mappings(id)).toMap
      val context = mapping.toSeq.sortBy(_._1.uniqueName).map(_._2)

      val tStart = System.currentTimeMillis

      val newCtx = ctx.copy(options = ctx.options.map {
        case LeonOption(optDef, value) if optDef == UnrollingProcedure.optFeelingLucky =>
          LeonOption(optDef)(false)
        case opt => opt
      })

      val solverf = SolverFactory.getFromSettings(newCtx, program).withTimeout(1.second)
      val solver  = solverf.getNewSolver()

      try {
        val cnstr = Not(replaceFromIDs(mapping, body))
        solver.assertCnstr(cnstr)

        gctx.model match {
          case pm: PartialModel =>
            val quantifiers = fargs.map(_.id).toSet
            val quorums = extractQuorums(body, quantifiers)

            val domainCnstr = orJoin(quorums.map { quorum =>
              val quantifierDomains = quorum.flatMap { case (path, caller, args) =>
                val optMatcher = e(caller) match {
                  case Stream(l: Lambda) => Some(gctx.lambdas.getOrElse(l, l))
                  case Stream(ev) => Some(ev)
                  case _ => None
                }

                optMatcher.toSeq.flatMap { matcher =>
                  val domain = pm.domains.get(matcher)
                  args.zipWithIndex.flatMap {
                    case (Variable(id),idx) if quantifiers(id) =>
                      Some(id -> domain.map(cargs => path -> cargs(idx)))
                    case _ => None
                  }
                }
              }

              val domainMap = quantifierDomains.groupBy(_._1).mapValues(_.map(_._2).flatten)
              andJoin(domainMap.toSeq.map { case (id, dom) =>
                orJoin(dom.toSeq.map { case (path, value) =>
                  // @nv: Note that equality is allowed here because of first-order quantifiers.
                  //      See [[leon.codegen.runtime.Monitor]] for more details.
                  path and Equals(Variable(id), value)
                })
              })
            })

            solver.assertCnstr(domainCnstr)

          case _ =>
        }

        solver.check match {
          case Some(negRes) =>
            val total = System.currentTimeMillis-tStart
            val res = BooleanLiteral(!negRes)
            ctx.reporter.debug("Verification took "+total+"ms")
            ctx.reporter.debug("Finished forall evaluation with: "+res)
            Stream(res)
          case _ =>
            Stream()
        }
      } catch {
        case e: Throwable => Stream()
      } finally {
        solverf.reclaim(solver)
        solverf.shutdown()
      }

    case p : Passes =>
      e(p.asConstraint)

    case choose: Choose =>

      // TODO add memoization
      implicit val debugSection = utils.DebugSectionSynthesis

      val p = synthesis.Problem.fromSpec(choose.pred)

      ctx.reporter.debug("Executing choose!")

      val tStart = System.currentTimeMillis

      val newCtx = ctx.copy(options = ctx.options.map {
        case LeonOption(optDef, value) if optDef == UnrollingProcedure.optFeelingLucky =>
          LeonOption(optDef)(false)
        case opt => opt
      })

      val solverf = SolverFactory.getFromSettings(newCtx, program)
      val solver  = solverf.getNewSolver()

      try {
        val eqs = p.as.map {
          case id => Equals(Variable(id), rctx.mappings(id))
        }

        val cnstr = p.pc withBindings p.as.map(id => id -> rctx.mappings(id)) and p.phi
        solver.assertCnstr(cnstr)

        def getSolution = try {
          solver.check match {
            case Some(true) =>
              val model = solver.getModel

              val valModel = valuateWithModel(model) _

              val res = p.xs.map(valModel)
              val leonRes = tupleWrap(res)
              val total = System.currentTimeMillis - tStart

              ctx.reporter.debug("Synthesis took " + total + "ms")
              ctx.reporter.debug("Finished synthesis with " + leonRes.asString)

              Some(leonRes)
            case _ =>
              None
          }
        } catch {
          case _: Throwable => None
        }

        Stream.iterate(getSolution)(prev => {
          val ensureDistinct = Not(Equals(tupleWrap(p.xs.map{ _.toVariable}), prev.get))
          solver.assertCnstr(ensureDistinct)
          val sol = getSolution
          // Clean up when the stream ends
          if (sol.isEmpty) {
            solverf.reclaim(solver)
            solverf.shutdown()
          }
          sol
        }).takeWhile(_.isDefined).take(10).map(_.get)
        // This take(10) is there because we are not working well with infinite streams yet...
      } catch {
        case e: Throwable =>
          solverf.reclaim(solver)
          solverf.shutdown()
          Stream()
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
          case (UnapplyPattern(ob, unapplyFun, subs), scrut) =>
            e(functionInvocation(unapplyFun.fd, Seq(scrut))) flatMap {
              case CaseClass(CaseClassType(cd, _), Seq()) if cd == program.library.None.get =>
                None
              case CaseClass(CaseClassType(cd, _), Seq(arg)) if cd == program.library.Some.get =>
                val subMaps = subs zip unwrapTuple(arg, subs.size) map {
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
          case _: RuntimeError =>
            // EvalErrors stop the computation altogether
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
        case (FiniteBag(el1, _), FiniteBag(el2, _)) => BooleanLiteral(el1 == el2)
        case (FiniteMap(el1, _, _), FiniteMap(el2, _, _)) => BooleanLiteral(el1.toSet == el2.toSet)
        case (FiniteLambda(m1, d1, _), FiniteLambda(m2, d2, _)) => BooleanLiteral(m1.toSet == m2.toSet && d1 == d2)
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

    case (Minus(_, _), Seq(InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2))) =>
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

    case (UMinus(_), Seq(InfiniteIntegerLiteral(i))) =>
      InfiniteIntegerLiteral(-i)

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
        case (a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) =>
          val FractionalLiteral(n, _) = e(RealMinus(a, b)).head
          BooleanLiteral(n >= 0)
        case (CharLiteral(c1), CharLiteral(c2)) => BooleanLiteral(c1 >= c2)
        case (le, re) => throw EvalError(typeErrorMsg(le, Int32Type))
      }

    case (IsTyped(sa @ SetAdd(_, _), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(elem, tpe2)
    )) =>
      FiniteSet(
        els1 + elem,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(sa, tpe)))
      )

    case (IsTyped(su @ SetUnion(s1, s2), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(FiniteSet(els2, _), SetType(tpe2))
    )) =>
      FiniteSet(
        els1 ++ els2,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(su, tpe)))
      )

    case (IsTyped(su @ SetIntersection(s1, s2), tpe), Seq(
      IsTyped(FiniteSet(els1, _), SetType(tpe1)),
      IsTyped(FiniteSet(els2, _), SetType(tpe2))
    )) =>
      FiniteSet(
        els1 & els2,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(su, tpe)))
      )

    case (IsTyped(su @ SetDifference(s1, s2), tpe), Seq(
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

    case (IsTyped(ba @ BagAdd(_, _), tpe), Seq(
      IsTyped(FiniteBag(els1, _), BagType(tpe1)),
      IsTyped(e, tpe2)
    )) =>
      FiniteBag(
        els1 + (e -> (els1.getOrElse(e, InfiniteIntegerLiteral(0)) match {
          case InfiniteIntegerLiteral(i) => InfiniteIntegerLiteral(i + 1)
          case il => throw EvalError(typeErrorMsg(il, IntegerType))
        })),
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(ba, tpe)))
      )

    case (IsTyped(bu @ BagUnion(b1, b2), tpe), Seq(
      IsTyped(FiniteBag(els1, _), BagType(tpe1)),
      IsTyped(FiniteBag(els2, _), BagType(tpe2))
    )) =>
      FiniteBag(
        (els1.keys ++ els2.keys).map(k => k -> {
          ((els1.getOrElse(k, InfiniteIntegerLiteral(0)), els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
            case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => InfiniteIntegerLiteral(i1 + i2)
            case (l, r) => throw EvalError(typeErrorMsg(l, IntegerType))
          })
        }).toMap,
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(bu, tpe)))
      )

    case (IsTyped(bi @ BagIntersection(s1, s2), tpe), Seq(
      IsTyped(FiniteBag(els1, _), BagType(tpe1)),
      IsTyped(FiniteBag(els2, _), BagType(tpe2))
    )) =>
      FiniteBag(
        els1.flatMap { case (k, e) => 
          val res = (e, els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
            case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => i1 min i2
            case (l, r) => throw EvalError(typeErrorMsg(l, IntegerType))
          }
          if (res <= 0) None else Some(k -> InfiniteIntegerLiteral(res))
        },
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(bi, tpe)))
      )

    case (IsTyped(bd @ BagDifference(s1, s2), tpe), Seq(
      IsTyped(FiniteBag(els1, _), BagType(tpe1)),
      IsTyped(FiniteBag(els2, _), BagType(tpe2))
    )) =>
      FiniteBag(
        els1.flatMap { case (k, e) =>
          val res = (e, els2.getOrElse(k, InfiniteIntegerLiteral(0))) match {
            case (InfiniteIntegerLiteral(i1), InfiniteIntegerLiteral(i2)) => i1 - i2
            case (l, r) => throw EvalError(typeErrorMsg(l, IntegerType))
          }
          if (res <= 0) None else Some(k -> InfiniteIntegerLiteral(res))
        },
        leastUpperBound(tpe1, tpe2).getOrElse(throw EvalError(typeErrorMsg(bd, tpe)))
      )

    case (MultiplicityInBag(_, _), Seq(e, FiniteBag(els, _))) =>
      els.getOrElse(e, InfiniteIntegerLiteral(0))

    case (fb @ FiniteBag(_, _), els) =>
      val Operator(_, builder) = fb
      builder(els)

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

    case (fa @ FiniteArray(_, _, _), subs) =>
      val Operator(_, builder) = fa
      builder(subs)

    case (fm @ FiniteMap(_, _, _), subs) =>
      val Operator(_, builder) = fm
      builder(subs)

    case (g @ MapApply(_, _), Seq(FiniteMap(m, _, _), k)) =>
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
      context.reporter.error(other.getPos, "Error: don't know how to handle " + other.asString + " in Evaluator ("+other.getClass+").")
      throw EvalError("Unhandled case in Evaluator: " + other.asString)

  }

}
