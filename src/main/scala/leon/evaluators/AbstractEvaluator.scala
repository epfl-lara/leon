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
  /** True if Application(Lambda(), ...)  have to be simplified. */
  var evaluateApplications = true
  
  // Used to make the final mkString for maps, sets, and bags. First column is the key to sort the expression on, second are the values and third are the trees.
  protected def mkString(elements: List[(String, Expr, Expr)], infix: (Expr, Expr)): (Expr, Expr) = {
    val (infix_value, infix_tree) = infix
    val (sorting_key, elements_value, elements_tree) = elements.sortBy(f => f._1).unzip3
    
    val fst = infix_value match {
      case StringLiteral(v) if elements_value.forall(_.isInstanceOf[StringLiteral]) =>
        StringLiteral(elements_value.map(_.asInstanceOf[StringLiteral].value).mkString(v))
      case infix_value =>
        elements_value match {
          case Nil => StringLiteral("")
          case a::q => q.foldLeft(a: Expr){ case (a, s) => StringConcat(StringConcat(a, infix_value), s) }
        }
    }
    
    val snd = elements_tree match {
      case Nil => StringLiteral("")
      case a::q => q.foldLeft(a){ case (a, s) => StringConcat(StringConcat(a, infix_tree), s) }
    }
    (fst, snd)
  }
  
  protected def e(expr: Expr)(implicit rctx: RC, gctx: GC): (Expr, Expr) = {
    implicit def aToC: AbstractEvaluator.this.underlying.RC = DefaultRecContext(rctx.mappings.filter{ case (k, v) => ExprOps.isValue(v) })
    expr match {
    case Variable(id) =>
      (rctx.mappings.get(id), rctx.mappingsAbstract.get(id)) match {
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
    
    case FunctionInvocation(TypedFunDef(fd, Seq(ta, tb)), Seq(mp, inkv, betweenkv, fk, fv)) if fd == program.library.mapMkString.get =>
      val (inkv_str, inkv_tree) = e(inkv)
      val infix = e(betweenkv)
      val (mp_map, mp_tree) = e(mp) match {
        case (FiniteMap(theMap, keyType, valueType), t) => (theMap, t)
        case (e, f) => 
          println("First argument is not a finite map: " + e)
          throw EvalError(typeErrorMsg(mp, MapType(ta, tb)))
      }
      
      val res1 = mp_map.toList.map{ case (k, v) =>
        val (kvalue, ktree) = e(application(fk, Seq(k)))
        val (vvalue, vtree) = e(application(fv, Seq(v)))
        val abs_value = StringConcat(StringConcat(ktree, inkv_tree), vtree)
        kvalue match {
          case StringLiteral(k) =>
            if(ExprOps.isValue(vvalue) && ExprOps.isValue(inkv_str)) {
              underlying.e(StringConcat(StringConcat(kvalue, inkv_str), vvalue)) match {
                case sl@StringLiteral(s) => (s, sl, abs_value)
                case e => throw RuntimeError("Not a string literal: " + e)
              }
            } else {
              (k, StringConcat(StringConcat(kvalue, inkv_str), vvalue), abs_value)
            }
          case _ =>
            throw RuntimeError("cannot infer the order on which to print the map " + mp_map)
        }
      }
      
      mkString(res1, infix)
        
    case FunctionInvocation(TypedFunDef(fd, Seq(ta)), Seq(mp, inf, f)) if fd == program.library.setMkString.get =>
      val infix = e(inf)
      val (mp_set, mp_tree) = e(mp) match { case (FiniteSet(elems, valueType), t) => (elems, t) case _ => throw EvalError(typeErrorMsg(mp, SetType(ta))) }
      
      val res = mp_set.toList.map{ case v =>
        e(application(f, Seq(v))) match { case (sl@StringLiteral(s), t) => (s, sl, t)
          case _ => throw EvalError(typeErrorMsg(v, StringType)) } }
      
      mkString(res, infix)
        
    case FunctionInvocation(TypedFunDef(fd, Seq(ta)), Seq(mp, inf, f)) if fd == program.library.bagMkString.get =>
      val infix = e(inf)
      val (mp_bag, mp_tree) = e(mp) match { case (FiniteBag(elems, valueType), t) => (elems, t) case _ => throw EvalError(typeErrorMsg(mp, SetType(ta))) }
      
      val res = mp_bag.toList.flatMap{ case (k, v) =>
        val fk = (e(application(f, Seq(k))) match { case (sl@StringLiteral(s), t) => (s, sl, t) case _ => throw EvalError(typeErrorMsg(k, StringType)) })
        val times = (e(v)) match { case (InfiniteIntegerLiteral(i), t) => i case _ => throw EvalError(typeErrorMsg(k, IntegerType)) }
        List.fill(times.toString.toInt)(fk)
      }

      mkString(res, infix)

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
      ecaller match {
        case l @ Lambda(params, body) if evaluateApplications =>
          val mapping = (params map (_.id) zip nargs).toMap
          e(body)(rctx.withNewVars2(mapping), gctx)
        case _ =>
          val abs_value = Application(tcaller, targs)
          if (ExprOps.isValue(ecaller) && (eargs forall ExprOps.isValue)) {
            (underlying.e(Application(ecaller, eargs)), abs_value)
          } else {
            (Application(ecaller, eargs), abs_value)
          }
      }
      
    case l @ Lambda(_, _) =>
      import ExprOps._
      val mapping = variablesOf(l).map(id => id -> e(Variable(id))).toMap
      (
      replaceFromIDs(mapping.mapValues(_._1), l).asInstanceOf[Lambda],
      replaceFromIDs(mapping.mapValues(_._2), l).asInstanceOf[Lambda])

    case Operator(es, builder) =>
      val (ees, ts) = es.map(e).unzip
      if(ees forall ExprOps.isValue) {
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
        
        (conc_value, final_abs_value)
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
                case AsInstanceOf(CaseClass(ct, args), _) if evaluateCaseClassSelector =>
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
                case Tuple(args) if evaluateCaseClassSelector=>
                  matchesPattern(s, a, args(i))
                case _ =>
                  matchesPattern(s, a, TupleSelect(exprFromScrut, i+1))
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
