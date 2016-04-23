/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package evaluators

import purescala.Extractors.Operator
import purescala.Constructors._
import purescala.Expressions._
import purescala.Types._
import purescala.Common.Identifier
import purescala.Definitions.{TypedFunDef, Program}
import purescala.DefOps
import purescala.TypeOps
import purescala.ExprOps
import purescala.Expressions.Expr
import leon.utils.DebugSectionSynthesis

case class AbstractRecContext(mappings: Map[Identifier, Expr], mappingsAbstract: Map[Identifier, Expr]) extends RecContext[AbstractRecContext] {
  def newVars(news: Map[Identifier, Expr], newsAbstract: Map[Identifier, Expr]): AbstractRecContext = copy(news, newsAbstract)
  def newVars(news: Map[Identifier, Expr]): AbstractRecContext = copy(news, news)
  
  def withNewVar(id: Identifier, v: (Expr, Expr)): AbstractRecContext = {
    newVars(mappings + (id -> v._1), mappingsAbstract + (id -> v._2))
  }

  def withNewVars2(news: Map[Identifier, (Expr, Expr)]): AbstractRecContext = {
    newVars(mappings ++ news.mapValues(_._1), mappingsAbstract ++ news.mapValues(_._2))
  }
  
  override def withNewVar(id: Identifier, v: Expr): AbstractRecContext = {
    newVars(mappings + (id -> v), mappingsAbstract + (id -> v))
  }
  
  override def withNewVars(news: Map[Identifier, Expr]): AbstractRecContext = {
    newVars(mappings ++ news, mappingsAbstract ++ news)
  }
}


trait HasAbstractRecContext extends ContextualEvaluator {
  type RC = AbstractRecContext
  def initRC(mappings: Map[Identifier, Expr]) = AbstractRecContext(mappings, mappings)
}

/** The evaluation returns a pair (e, t),
 *  where e is the expression evaluated as much as possible, and t is the way the expression has been evaluated.
 *  Caution: If and Match statement require the condition to be non-abstract. */
class AbstractEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with HasDefaultGlobalContext with HasAbstractRecContext {
  lazy val scalaEv = new ScalacEvaluator(underlying, ctx, prog)
  
  /** Evaluates resuts which can be evaluated directly
    * For example, concatenation of two string literals */
  val underlying = new DefaultEvaluator(ctx, prog)
  underlying.setEvaluationFailOnChoose(true)
  override type Value = (Expr, Expr)

  override val description: String = "Evaluates string programs but keeps the formula which generated the value"
  override val name: String = "Abstract evaluator"
 
  /** True if CaseClassSelector(...CaseClass(...))  have to be simplified. */
  var evaluateCaseClassSelector = true
  
  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): (Expr, Expr) = {
    implicit def aToC: AbstractEvaluator.this.underlying.RC = DefaultRecContext(rctx.mappings)
    expr match {
    case Variable(id) =>
      (rctx.mappings.get(id), rctx.mappingsAbstract.get(id)) match {
        case (Some(v), None) if v != expr => // We further evaluate v to make sure it is a value
          e(v)
        case (Some(v), Some(va)) if v != expr =>
          (e(v)._1, va)
        case (Some(v), Some(va)) =>
          (v, va)
        case _ =>
          (expr, expr)
      }

    case e if ExprOps.isValue(e) =>
      (e, e)
      
    case IfExpr(cond, thenn, elze) =>
      val first = underlying.e(cond)
      first match {
        case BooleanLiteral(true) =>
          ctx.reporter.ifDebug(printer => printer(thenn))(DebugSectionSynthesis)
          e(thenn)
        case BooleanLiteral(false) => e(elze)
        case _ => throw EvalError(typeErrorMsg(first, BooleanType))
      }
      
    case MatchExpr(scrut, cases) =>
      val (escrut, tscrut) = e(scrut)
      cases.toStream.map(c => matchesCaseAbstract(escrut, tscrut, c)).find(_.nonEmpty) match {
        case Some(Some((c, mappings))) => e(c.rhs)(rctx.withNewVars2(mappings), gctx)
        case _ => throw RuntimeError("MatchError(Abstract evaluation): "+escrut.asString+" did not match any of the cases :\n" + cases.mkString("\n"))
      }

    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1
      val evArgs = args map e
      val evArgsValues = evArgs.map(_._1)
      val evArgsOrigin = evArgs.map(_._2)
      
      // build a mapping for the function...
      val frame = rctx.withNewVars2((tfd.paramIds zip evArgs).toMap)
  
      val callResult = if ((evArgsValues forall ExprOps.isValue) && tfd.fd.annotations("extern") && ctx.classDir.isDefined) {
        (scalaEv.call(tfd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
      } else {
        if((!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) || tfd.body.exists(b => ExprOps.exists(e => e.isInstanceOf[Choose])(b))) {
          (functionInvocation(tfd.fd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
        } else {
          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          try {
            e(body)(frame, gctx)
          } catch {
            case e: RuntimeError => (functionInvocation(tfd.fd, evArgsValues), functionInvocation(tfd.fd, evArgsOrigin))
          }
        }
      }
      callResult

    case Let(i, ex, b) =>
      val (first, second) = e(ex)
      e(b)(rctx.withNewVar(i, (first, second)), gctx)

    case Application(caller, args) =>
      val (ecaller, tcaller) = e(caller)
      val nargs = args map e
      val (eargs, targs) = nargs.unzip
      val abs_value = Application(tcaller, targs)
      if (ExprOps.isValue(ecaller) && (eargs forall ExprOps.isValue)) {
        (underlying.e(Application(ecaller, eargs)), abs_value)
      } else ecaller match {
        case l @ Lambda(params, body) =>
          val mapping = (params map (_.id) zip nargs).toMap
          e(body)(rctx.withNewVars2(mapping), gctx)
        case _ =>
          (Application(ecaller, eargs), abs_value)
      }

    case Operator(es, builder) =>
      val (ees, ts) = es.map(e).unzip
      if(ees forall ExprOps.isValue) {
        val conc_value = underlying.e(builder(ees))
        val abs_value = builder(ts)
        (conc_value, abs_value)
      } else {
        (builder(ees), builder(ts))
      }
    }
  }

  def matchesCaseAbstract(scrut: Expr, abstractScrut: Expr, caze: MatchCase)(implicit rctx: RC, gctx: GC): Option[(MatchCase, Map[Identifier, (Expr, Expr)])] = {
    import purescala.TypeOps.isSubtypeOf
    import purescala.Extractors._

    def matchesPattern(pat: Pattern, expr: Expr, exprFromScrut: Expr): Option[Map[Identifier, (Expr, Expr)]] = (pat, expr) match {
      case (InstanceOfPattern(ob, pct), e) =>
        if (isSubtypeOf(e.getType, pct)) {
          Some(obind(ob, e, AsInstanceOf(exprFromScrut, pct)))
        } else {
          None
        }
      case (WildcardPattern(ob), e) =>
        Some(obind(ob, e, exprFromScrut))

      case (CaseClassPattern(ob, pct, subs), CaseClass(ct, args)) =>
        if (pct == ct) {
          val res = (subs zip args zip ct.classDef.fieldsIds).map{
            case ((s, a), id) =>
              exprFromScrut match {
                case CaseClass(ct, args) if evaluateCaseClassSelector =>
                  matchesPattern(s, a, args(ct.classDef.selectorID2Index(id)))
                case _ =>
                  matchesPattern(s, a, CaseClassSelector(ct, exprFromScrut, id))
              }
          }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr, exprFromScrut) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (up @ UnapplyPattern(ob, _, subs), scrut) =>
        e(functionInvocation(up.unapplyFun.fd, Seq(scrut))) match {
          case (CaseClass(CaseClassType(cd, _), Seq()), eBuilt) if cd == program.library.None.get =>
            None
          case (CaseClass(CaseClassType(cd, _), Seq(arg)), eBuilt) if cd == program.library.Some.get =>
            val res = (subs zip unwrapTuple(arg, subs.size)).zipWithIndex map {
              case ((s, a), i) => matchesPattern(s, a, tupleSelect(eBuilt, i + 1, subs.size))
            }
            if (res.forall(_.isDefined)) {
              Some(obind(ob, expr, eBuilt) ++ res.flatten.flatten)
            } else {
              None
            }
          case other =>
            throw EvalError(typeErrorMsg(other._1, up.unapplyFun.returnType))
        }
      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args).zipWithIndex.map{
            case ((s, a), i) =>
              exprFromScrut match {
                case TupleSelect(Tuple(args), i) if evaluateCaseClassSelector=>
                  matchesPattern(s, a, args(i - 1))
                case _ =>
                  matchesPattern(s, a, TupleSelect(exprFromScrut, i + 1))
              }
          }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr, exprFromScrut) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (LiteralPattern(ob, l1) , l2 : Literal[_]) if l1 == l2 =>
        Some(obind(ob, l1, exprFromScrut))
      case _ => None
    }

    def obind(ob: Option[Identifier], e: Expr, eBuilder: Expr): Map[Identifier, (Expr, Expr)] = {
      Map[Identifier, (Expr, Expr)]() ++ ob.map(id => id -> ((e, eBuilder)))
    }

    caze match {
      case SimpleCase(p, rhs) =>
        matchesPattern(p, scrut, abstractScrut).map(r =>
          (caze, r)
        )

      case GuardedCase(p, g, rhs) =>
        for {
          r <- matchesPattern(p, scrut, abstractScrut)
          if e(g)(rctx.withNewVars2(r), gctx)._1 == BooleanLiteral(true)
        } yield (caze, r)
    }
  }
}
