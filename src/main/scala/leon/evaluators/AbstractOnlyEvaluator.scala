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

case class AbstractOnlyRecContext(concMapping: DefaultRecContext, mappingsAbstractOnly: Map[Identifier, Expr]) extends RecContext[AbstractOnlyRecContext] {
  def newVars(news: Map[Identifier, Expr], newsAbstractOnly: Map[Identifier, Expr]): AbstractOnlyRecContext = copy(concMapping.newVars(news), newsAbstractOnly)
  def newVars(news: Map[Identifier, Expr]): AbstractOnlyRecContext = copy(concMapping.newVars(news), news)
  def mappings = concMapping.mappings
  
  def withNewVar(id: Identifier, v: Expr, vAbs: Expr): AbstractOnlyRecContext = {
    newVars(mappings + (id -> v), mappingsAbstractOnly + (id -> vAbs))
  }

  /*def withNewVars2(news: Map[Identifier, (Expr, Expr)]): AbstractOnlyRecContext = {
    newVars(mappings ++ news.mapValues(_._1), mappingsAbstractOnly ++ news.mapValues(_._2))
  }*/
  
  def withNewVars3(news: Map[Identifier, Expr], newsAbstract: Map[Identifier, Expr]): AbstractOnlyRecContext = {
    newVars(concMapping.mappings ++ news, mappingsAbstractOnly ++ newsAbstract)
  }
  
  override def withNewVar(id: Identifier, v: Expr): AbstractOnlyRecContext = {
    newVars(mappings + (id -> v), mappingsAbstractOnly + (id -> v))
  }
  
  override def withNewVars(news: Map[Identifier, Expr]): AbstractOnlyRecContext = {
    newVars(mappings ++ news, mappingsAbstractOnly ++ news)
  }
}


trait HasAbstractOnlyRecContext extends ContextualEvaluator {
  type RC = AbstractOnlyRecContext
  def initRC(mappings: Map[Identifier, Expr]) = AbstractOnlyRecContext(DefaultRecContext(mappings), mappings)
}

/** The evaluation returns only the abstract value compared to the other implementation of [[leon.evaluators.AbstractEvaluator AbstractEvaluator]]
 *  It also supposes that everything can be computed else (i.e. not possible to add non-bound variables)
 *  @returns the way the expression has been evaluated. */
class AbstractOnlyEvaluator(ctx: LeonContext, prog: Program) extends ContextualEvaluator(ctx, prog, 50000) with HasDefaultGlobalContext with HasAbstractOnlyRecContext {
  lazy val scalaEv = new ScalacEvaluator(underlying, ctx, prog)
  
  /** Evaluates resuts which can be evaluated directly
    * For example, concatenation of two string literals */
  val underlying = new DefaultEvaluator(ctx, prog)
  underlying.setEvaluationFailOnChoose(true)
  override type Value = Expr

  override val description: String = "Evaluates string programs but keeps the formula which generated the value"
  override val name: String = "AbstractOnly evaluator"
 
  /** True if CaseClassSelector(...CaseClass(...))  have to be simplified. */
  var evaluateCaseClassSelector = true
  /** True if Application(Lambda(), ...)  have to be simplified. */
  var evaluateApplications = true
  
  implicit def aToC(implicit rctx: RC): AbstractOnlyEvaluator.this.underlying.RC = rctx.concMapping

  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = {
    expr match {
    case Variable(id) =>
      rctx.mappingsAbstractOnly.get(id) match {
        case Some(va) =>
          (va)
        case _ =>
          expr
      }

    case e : Literal[_] =>
      e
      
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
      val escrut = underlying.e(scrut)
      val tscrut = e(scrut)
      cases.toStream.map(c => matchesCaseAbstractOnly(escrut, tscrut, c)).find(_.nonEmpty) match {
        case Some(Some((c, mappings))) => e(c.rhs)(rctx.withNewVars3(mappings.map(v => v._1 -> underlying.e(v._2)).toMap, mappings.toMap), gctx)
        case _ => throw RuntimeError("MatchError(AbstractOnly evaluation): "+escrut.asString+" did not match any of the cases :\n" + cases.mkString("\n"))
      }

    case FunctionInvocation(tfd, args) =>
      if (gctx.stepsLeft < 0) {
        throw RuntimeError("Exceeded number of allocated methods calls ("+gctx.maxSteps+")")
      }
      gctx.stepsLeft -= 1
      
      val evArgsValues = args map (underlying.e)
      val evArgsOrigin = args map e
      
      // build a mapping for the function...
      //val frame = rctx.withNewVars2((tfd.paramIds zip evArgs).toMap)
  
      val callResult = if (tfd.fd.annotations("extern") && ctx.classDir.isDefined) {
        functionInvocation(tfd.fd, evArgsOrigin)
      } else {
        if((!tfd.hasBody && !rctx.mappings.isDefinedAt(tfd.id)) || tfd.body.exists(b => ExprOps.exists(e => e.isInstanceOf[Choose])(b))) {
          functionInvocation(tfd.fd, evArgsOrigin)
        } else {
          val body = tfd.body.getOrElse(rctx.mappings(tfd.id))
          try {
            val frame = rctx.withNewVars3((tfd.paramIds zip evArgsValues).toMap, (tfd.paramIds zip evArgsOrigin).toMap)
            e(body)(frame, gctx)
          } catch {
            case e: Throwable => 
              //println("Error during execution of " + expr + ": " + e)
              //println(e.getStackTrace.map(_.toString).mkString("\n"))
              functionInvocation(tfd.fd, evArgsOrigin)
          }
        }
      }
      callResult

    case Let(i, ex, b) =>
      val first = underlying.e(ex)
      val second = e(ex)
      e(b)(rctx.withNewVar(i, first, second), gctx)

    case Application(caller, args) =>
      val ecaller = underlying.e(caller)
      val tcaller = e(caller)
      val targs = args map e
      val eargs = args map underlying.e
      ecaller match {
        case l @ Lambda(params, body) if evaluateApplications =>
          val mapping    = (params map (_.id) zip eargs).toMap
          val mappingAbs = (params map (_.id) zip targs).toMap
          e(body)(rctx.withNewVars3(mapping, mappingAbs), gctx)
        case _ =>
          Application(tcaller, targs)
      }
      
    case l @ Lambda(_, _) =>
      import ExprOps._
      val mapping = variablesOf(l).map(id => id -> e(Variable(id))).toMap
      replaceFromIDs(mapping, l).asInstanceOf[Lambda]

    case Operator(es, builder) =>
      val ees = es.map(underlying.e)
      val ts = es.map(e)
        val conc_value = underlying.e(builder(ees))
        val abs_value = builder(ts)
        val final_abs_value = if( evaluateCaseClassSelector) {
        abs_value match {
          case CaseClassSelector(cct, CaseClass(ct, args), id) =>
            args(ct.classDef.selectorID2Index(id))
          case CaseClassSelector(cct, AsInstanceOf(CaseClass(ct, args), ccct), id) =>
            args(ct.classDef.selectorID2Index(id))
          case TupleSelect(Tuple(args), i) =>
            args(i-1)
          case e => e
        }
      } else abs_value
      
      final_abs_value
    }
  }

  def matchesCaseAbstractOnly(scrut: Expr, abstractScrut: Expr, caze: MatchCase)(implicit rctx: RC, gctx: GC): Option[(MatchCase, Iterable[(Identifier, Expr)])] = {
    import purescala.TypeOps.isSubtypeOf
    import purescala.Extractors._

    def matchesPattern(pat: Pattern, expr: Expr, exprFromScrut: Expr): Option[Iterable[(Identifier, Expr)]] = (pat, expr) match {
      case (InstanceOfPattern(ob, pct), _) =>
        if (isSubtypeOf(exprFromScrut.getType, pct)) {
          Some(obind(ob, exprFromScrut/*AsInstanceOf(exprFromScrut, pct)*/)) // is AsInstanceOf needed?
        } else {
          None
        }
      case (WildcardPattern(ob), _) =>
        Some(obind(ob, exprFromScrut))

      case (CaseClassPattern(ob, pct, subs), CaseClass(ct, args)) =>
        if (pct == ct) {
          val res = (subs zip args zip ct.classDef.fieldsIds).map{
            case ((s, a), id) =>
              exprFromScrut match {
                case CaseClass(ct, args) if evaluateCaseClassSelector =>
                  matchesPattern(s, a, args(ct.classDef.selectorID2Index(id)))
                case AsInstanceOf(CaseClass(ct, args), _) if evaluateCaseClassSelector =>
                  matchesPattern(s, a, args(ct.classDef.selectorID2Index(id)))
                case _ =>
                  matchesPattern(s, a, CaseClassSelector(ct, exprFromScrut, id))
              }
          }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, exprFromScrut) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (up @ UnapplyPattern(ob, _, subs), scrut) =>
        underlying.e(functionInvocation(up.unapplyFun.fd, Seq(scrut))) match {
          case CaseClass(CaseClassType(cd, _), Seq()) if cd == program.library.None.get =>
            None
          case CaseClass(CaseClassType(cd, _), Seq(arg)) if cd == program.library.Some.get =>
            val res = (subs zip unwrapTuple(arg, subs.size)).zipWithIndex map {
              case ((s, a), i) => matchesPattern(s, a, tupleSelect(arg, i + 1, subs.size))
            }
            if (res.forall(_.isDefined)) {
              Some(obind(ob, scrut) ++ res.flatten.flatten)
            } else {
              None
            }
          case other =>
            throw EvalError(typeErrorMsg(other, up.unapplyFun.returnType))
        }
      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args).zipWithIndex.map{
            case ((s, a), i) =>
              exprFromScrut match {
                case Tuple(args) if evaluateCaseClassSelector=>
                  matchesPattern(s, a, args(i))
                case _ =>
                  matchesPattern(s, a, TupleSelect(exprFromScrut, i+1))
              }
          }
          if (res.forall(_.isDefined)) {
            Some(obind(ob, exprFromScrut) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }
      case (LiteralPattern(ob, l1) , l2 : Literal[_]) if l1 == l2 =>
        Some(obind(ob, exprFromScrut))
      case _ => None
    }

    def obind(ob: Option[Identifier], eBuilder: Expr): Iterable[(Identifier, Expr)] = {
      ob.map(id => id -> (eBuilder)).toList
    }

    caze match {
      case SimpleCase(p, rhs) =>
        matchesPattern(p, scrut, abstractScrut).map(r =>
          (caze, r)
        )

      case GuardedCase(p, g, rhs) =>
        for {
          r <- matchesPattern(p, scrut, abstractScrut)
          if underlying.e(g)(rctx.concMapping.withNewVars(r.map(kv => kv._1 -> underlying.e(kv._2)).toMap), gctx) == BooleanLiteral(true)
        } yield (caze, r)
    }
  }
}
