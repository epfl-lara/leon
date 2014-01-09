/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.HOTreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

case class Invocation[T](fd: TypedFunDef, args: Seq[T])

trait GroundEvaluator[T] {
  def eval(funDef : TypedFunDef, args : Seq[T]) : Option[T]
}

class FunctionTemplate[T] (
  templateFactory    : TemplateFactory[T],
  val funDef         : TypedFunDef,
  val activatingBool : Identifier,
  condVars           : Set[Identifier],
  exprVars           : Set[Identifier],
  guardedExprs       : Map[Identifier, Seq[Expr]],
  resultMap          : Map[Identifier, Expr],
  applicationArgsIds : Seq[Identifier],
  isRealFunDef       : Boolean) {

  private val funDefArgsIds : Seq[Identifier] = funDef.args.map(_.id)
  private val constraintFactory = new ConstraintFactory(templateFactory)

  val fActivatingBool  : T = templateFactory.encode(activatingBool)

  private val zippedCondVars        : Seq[(Identifier, T)] = condVars.toSeq     map (id => id -> templateFactory.encode(id))
  private val zippedExprVars        : Seq[(Identifier, T)] = exprVars.toSeq     map (id => id -> templateFactory.encode(id))
  private val zippedFunDefArgs      : Seq[(Identifier, T)] = funDefArgsIds      map (id => id -> templateFactory.encode(id))
  private val zippedApplicationArgs : Seq[(Identifier, T)] = applicationArgsIds map (id => id -> templateFactory.encode(id))

  private val idToEncodedIds : Map[Identifier, T] = {
    Map(activatingBool -> fActivatingBool) ++
    zippedCondVars ++
    zippedExprVars ++
    zippedFunDefArgs ++
    zippedApplicationArgs
  }

  private val (asClauses, asHOClauses) : (Seq[Expr], Seq[(Identifier, Expr)]) = {
    val pairs = for ((b,es) <- guardedExprs.toSeq; e <- es) yield b -> e
    val (simplePairs, functionPairs) = pairs.toSeq.partition(p => !exists{
      case Variable(id) if resultMap.contains(id) => true
      case expr if expr.getType.isInstanceOf[FunctionType] => true
      case _ => false
    }(p._2))
    val simpleClauses = simplePairs.map(p => Implies(Variable(p._1), p._2))
    (simpleClauses, functionPairs)
  }

  private val encodedClauses : Seq[T] = asClauses.map(templateFactory.translate(_, idToEncodedIds))

  private val blockers : Map[Identifier,Set[FunctionInvocation]] = {
    val idCall = FunctionInvocation(funDef.fd, funDef.args.map(_.toVariable))

    Map((for((b, es) <- guardedExprs) yield {
      val calls = es.filter({
        e => !exists{ _.getType.isInstanceOf[FunctionType]}(e)
      }).foldLeft(Set.empty[FunctionInvocation])({
        (s,e) => s ++ functionCallsOf(e)
      }) - idCall

      if(calls.isEmpty) {
        None
      } else {
        Some(b -> calls)
      }
    }).flatten.toSeq : _*)
  }

  private val encodedBlockers : Map[T,Set[Invocation[T]]] = blockers.map {
    case (b, funs) => idToEncodedIds(b) -> (funs map { fi =>
      Invocation(TypedFunDef(fi.funDef, fi.tparams), fi.args.map(templateFactory.translate(_, idToEncodedIds)))
    })
  }

  // We use a cache to create the same boolean variables.
  private val cache : MutableMap[Seq[T],Map[T,T]] = MutableMap.empty

  def instantiate(aVar : T, args : Seq[T]) : (Seq[T], Map[T,Set[Invocation[T]]]) = {
    // For funDefs that return higher order functions, we store their applications as Invocations.
    // This means we must store the arguments of the enclosing function application in the Invocation,
    // so we may have more arguments then the actual funDef.args.size
    assert(args.size >= funDef.args.size)

    // The "isRealFunDef" part is to prevent evaluation of "fake"
    // function templates, as generated from FairZ3Solver.
    if (isRealFunDef) {
      val evaluation = templateFactory.evaluator.map(evaluator => evaluator.eval(funDef, args)).flatten
      if (evaluation.isDefined) return (Seq(evaluation.get), Map.empty)
    }
    // ...end of ground evaluation part.

    val (funDefArgs, applicationArgs) = args.splitAt(funDef.args.size)

    val (wasHit,baseIdSubstMap) = cache.get(args) match {
      case Some(m) => (true,m)
      case None =>
        val newMap : Map[T,T] = 
          (zippedExprVars ++ zippedCondVars).map(p => p._2 -> templateFactory.encode(p._1)).toMap ++
          (zippedFunDefArgs.map(_._2) zip funDefArgs) ++ (zippedApplicationArgs.map(_._2) zip applicationArgs)
        cache(args) = newMap
        (false,newMap)
    }

    val idSubstMap : Map[T,T] = baseIdSubstMap + (fActivatingBool -> aVar)
    val replace: T => T = templateFactory.replacer(idSubstMap)

    val newClauses  = encodedClauses.map(replace(_))
    val newBlockers = encodedBlockers.map({ case (b, funs) =>
      idSubstMap(b) -> funs.map(fi => fi.copy(args = fi.args.map(replace(_))))
    })

    // Translate Z3 arguments back to Leon trees if they are higher-order functions
    val ftArgs = ((funDefArgsIds ++ applicationArgsIds) zip args).filter(_._1.getType.isInstanceOf[FunctionType])
    val (asHOMap, closureVarMap) = ftArgs.map({ case (id, arg) =>
      val (function, closureVars) = templateFactory.getClosure(arg).get
      (id -> function, closureVars)
    }).unzip match {
      case (args, closures) =>
        (Map(args : _*), closures.foldLeft(Map[Identifier, T]())((acc,m) => acc ++ m))
    }

    // If this function returns higher-order functions, we setup the anonymous function encoding
    val applicationArgMap = Map(applicationArgsIds zip applicationArgs : _*)
    val applicationResultMap = resultMap.map({ entry =>
      entry._1 -> buildApplication(entry._2, applicationArgsIds.map(_.toVariable))
    })

    val bodySubstMap : Map[Identifier, T] = (idToEncodedIds ++ closureVarMap ++ applicationArgMap).mapValues(replace(_))

    case class ConstraintState(condVars      : Set[Identifier] = Set(),
                               exprVars      : Set[Identifier] = Set(),
                               guardedExprs  : Map[Identifier, Seq[Expr]] = Map(),
                               newIdSubstMap : Map[Identifier, T] = Map())

    // Generate invocation constraints...
    val clausesConstraintState = asHOClauses.foldLeft(ConstraintState()) {
      case (ConstraintState(condVars, exprVars, guardedExprs, newIdSubstMap), (b, expr)) =>
        val appExpr = replaceFromIDs(applicationResultMap, expr)
        val asHOAppExpr = replaceFromIDs(asHOMap, appExpr)
        val cleanExpr = preProcess(asHOAppExpr)
        val (newConstraints, newSubsts) = constraintFactory.required(cleanExpr, bodySubstMap)
        val newState = ConstraintState(condVars, exprVars, guardedExprs, newIdSubstMap ++ newSubsts)

        (newConstraints :+ cleanExpr).foldLeft(newState) { case (ConstraintState(conds, exprs, guarded, subst), expr) =>
          val (newConds, newExprs, newGuarded) = TemplateFactory.mkClauses(b, expr)
          val allGuarded = (guarded.keys ++ newGuarded.keys).map { key =>
            key -> (guarded.getOrElse(key, Seq()) ++ newGuarded.getOrElse(key, Seq()))
          }.toMap
          ConstraintState(conds ++ newConds, exprs ++ newExprs, allGuarded, subst)
        }
    }

    // ... and expand forall expressions in postcondition assumption
    val ConstraintState(newConds, newExprs, newGuarded, newIdSubstMap) =
      if (!funDef.returnType.isInstanceOf[FunctionType]) clausesConstraintState else {
        def manageFunctionArgument(id: Identifier): Expr = {
          if(!id.getType.isInstanceOf[FunctionType]) id.toVariable else asHOMap(id)
        }

        val fiIdCall = FunctionInvocation(funDef.fd, funDef.args.map(_.id) map manageFunctionArgument)
        val idCall = buildApplication(fiIdCall, applicationArgsIds map manageFunctionArgument).asInstanceOf[FunctionApplication]

        val (constraints, newIdSubstMap) = constraintFactory.assumed(idCall, bodySubstMap)
        val newState = clausesConstraintState.copy(newIdSubstMap = clausesConstraintState.newIdSubstMap ++ newIdSubstMap)

        constraints.foldLeft(newState) { case (ConstraintState(conds, exprs, guarded, subst), expr) =>
          val (newConds, newExprs, newGuarded) = TemplateFactory.mkClauses(activatingBool, expr)
          val allGuarded = (guarded.keys ++ newGuarded.keys).map { key =>
            key -> (guarded.getOrElse(key, Seq()) ++ newGuarded.getOrElse(key, Seq()))
          }.toMap
          ConstraintState(conds ++ newConds, exprs ++ newExprs, allGuarded, subst)
        }
      }

    // Extend substitution mapping with new condVars, exprVars, closures and higher-order result setup
    val varSubstMap = (newConds ++ newExprs).map(id => id -> templateFactory.encode(id))
    val boundIdSubstMap = bodySubstMap ++ varSubstMap ++ newIdSubstMap

    // Free variables may appear from forall statements in post-conditions, so they need to be encoded as well!
    val variables = (for((b,es) <- newGuarded; e <- es) yield variablesOf(e)).flatten.toSet
    val remainingVars = (variables -- boundIdSubstMap.keys).filter(!_.getType.isInstanceOf[FunctionType])
    val freeSubstMap = remainingVars.map(id => id -> templateFactory.encode(id))
    val allIdSubstMap = boundIdSubstMap ++ freeSubstMap

    // Remove closures from expressions before translating them so they can be retrieved later on
    val guarded = newGuarded.map { case (b, es) => b -> es.map(templateFactory.removeClosures(_, allIdSubstMap)) }

    val encodedHOClauses = for ((b,es) <- guarded; e <- es) yield templateFactory.translate(Implies(Variable(b), e), allIdSubstMap)

    val encodedHOBlockers : Map[T, Set[Invocation[T]]] = {
      def manageFunctionArgument(id: Identifier): Expr = {
        if(!id.getType.isInstanceOf[FunctionType]) id.toVariable else {
          templateFactory.removeClosures(asHOMap(id), allIdSubstMap)
        }
      }

      val fiIdCall = FunctionInvocation(funDef.fd, funDef.args.map(_.id) map manageFunctionArgument)
      val idCall = buildApplication(fiIdCall, applicationArgsIds map manageFunctionArgument)

      def collectBlockers(expr: Expr): Set[Invocation[T]] = {
        def funDefWithArgs(expr: Expr): Option[(TypedFunDef, Seq[Expr])] = expr match {
          case FunctionApplication(caller, args) => funDefWithArgs(caller) match {
            case Some((fd, fdArgs)) => Some((fd, fdArgs ++ args))
            case _ => None
          }
          case fi @ FunctionInvocation(fd, fdArgs) => Some((TypedFunDef(fd, fi.tparams), fdArgs))
          case _ => None
        }

        def rec(expr: Expr): Set[Invocation[T]] = {
          val opt = if (expr.getType.isInstanceOf[FunctionType]) None else funDefWithArgs(expr)
          val invocation = if (expr == idCall) None else opt.map { case (fd, args) => 
            Invocation(fd, args.map(templateFactory.translate(_, allIdSubstMap)))
          }

          (expr match {
            case NAryOperator(es, _) => es.flatMap(rec).toSet
            case BinaryOperator(e1, e2, _) => rec(e1) ++ rec(e2)
            case UnaryOperator(e, _) => rec(e)
            case (_ : Terminal) => Set.empty
            case _ => scala.sys.error("Unexpected expr: " + expr)
          }) ++ invocation
        }

        rec(expr)
      }

      Map((for((b, es) <- guarded) yield {
        val blockers = es.foldLeft(Set.empty[Invocation[T]])({ (s,e) =>
          s ++ collectBlockers(e)
        })

        if(blockers.isEmpty)  None else Some(allIdSubstMap(b) -> blockers)
      }).flatten.toSeq : _*)
    }

    val allClauses = newClauses ++ encodedHOClauses
    val allBlockers = (newBlockers.keys ++ encodedHOBlockers.keys).map({ key =>
      key -> (newBlockers.getOrElse(key, Set()) ++ encodedHOBlockers.getOrElse(key, Set()))
    }).toMap

    (allClauses, allBlockers)
  }

  override def toString : String = {
    "Template for def " + funDef.id + "(" + funDef.args.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + funDef.returnType + " is :\n" +
    " * Activating boolean : " + activatingBool + "\n" + 
    " * Control booleans   : " + condVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * Expression vars    : " + exprVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * \"Clauses\"          : " + "\n    " + asClauses.mkString("\n    ") + "\n" +
    " * \"HO Clauses\"       : " + "\n    " + asHOClauses.mkString("\n    ") + "\n" +
    " * Block-map          : " + blockers.toString + "\n" +
    " * Result-map         : " + resultMap.toString + "\n" +
    " * Application vars   : " + applicationArgsIds.toString
  }
}

