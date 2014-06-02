/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import utils._
import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

class FunctionTemplate[T](
  val tfd: TypedFunDef,
  val encoder: TemplateEncoder[T],
  activatingBool: Identifier,
  condVars: Set[Identifier],
  exprVars: Set[Identifier],
  guardedExprs: Map[Identifier,Seq[Expr]],
  isRealFunDef: Boolean) {

  val evalGroundApps = false

  val clauses: Seq[Expr] = {
    (for((b,es) <- guardedExprs; e <- es) yield {
      Implies(Variable(b), e)
    }).toSeq
  }

  val trActivatingBool = encoder.encodeId(activatingBool)

  val trFunDefArgs     = tfd.params.map( ad => encoder.encodeId(ad.id))
  val zippedCondVars   = condVars.map(id => (id -> encoder.encodeId(id)))
  val zippedExprVars   = exprVars.map(id => (id -> encoder.encodeId(id)))
  val zippedFunDefArgs = tfd.params.map(_.id) zip trFunDefArgs

  val idToTrId: Map[Identifier, T] = {
    Map(activatingBool -> trActivatingBool) ++
    zippedCondVars ++
    zippedExprVars ++
    zippedFunDefArgs
  }

  val encodeExpr = encoder.encodeExpr(idToTrId) _

  val trClauses: Seq[T] = clauses.map(encodeExpr)

  val trBlockers: Map[T, Set[TemplateCallInfo[T]]] = {
    val idCall = TemplateCallInfo[T](tfd, trFunDefArgs)

    Map((for((b, es) <- guardedExprs) yield {
      val allCalls = es.map(functionCallsOf).flatten.toSet
      val calls = (for (c <- allCalls) yield {
        TemplateCallInfo[T](c.tfd, c.args.map(encodeExpr))
      }) - idCall

      if(calls.isEmpty) {
        None
      } else {
        Some(idToTrId(b) -> calls)
      }
    }).flatten.toSeq : _*)
  }

  // We use a cache to create the same boolean variables.
  var cache = Map[Seq[T], Map[T, T]]()

  def instantiate(aVar: T, args: Seq[T]): (Seq[T], Map[T, Set[TemplateCallInfo[T]]]) = {
    assert(args.size == tfd.params.size)

    // The "isRealFunDef" part is to prevent evaluation of "fake"
    // function templates, as generated from FairZ3Solver.
    //if(evalGroundApps && isRealFunDef) {
    //  val ga = args.view.map(solver.asGround)
    //  if(ga.forall(_.isDefined)) {
    //    val leonArgs = ga.map(_.get).force
    //    val invocation = FunctionInvocation(tfd, leonArgs)
    //    solver.getEvaluator.eval(invocation) match {
    //      case EvaluationResults.Successful(result) =>
    //        val z3Invocation = z3.mkApp(solver.functionDefToDecl(tfd), args: _*)
    //        val z3Value      = solver.toZ3Formula(result).get
    //        val asZ3         = z3.mkEq(z3Invocation, z3Value)
    //        return (Seq(asZ3), Map.empty)

    //      case _ => throw new Exception("Evaluation of ground term should have succeeded.")
    //    }
    //  }
    //}
    // ...end of ground evaluation part.

    val baseSubstMap = cache.get(args) match {
      case Some(m) => m
      case None =>
        val newMap: Map[T, T] =
          (zippedCondVars ++ zippedExprVars).map{ case (id, idT) => idT -> encoder.encodeId(id) }.toMap ++
          (trFunDefArgs zip args)

        cache += args -> newMap
        newMap
    }

    val substMap : Map[T, T] = baseSubstMap + (trActivatingBool -> aVar)

    val substituter = encoder.substitute(substMap)

    val newClauses  = trClauses.map(substituter)

    val newBlockers = trBlockers.map { case (b, funs) =>
      val bp = substituter(b)

      val newFuns = funs.map(fi => fi.copy(args = fi.args.map(substituter)))

      bp -> newFuns
    }

    (newClauses, newBlockers)
  }

  override def toString : String = {
    "Template for def " + tfd.signature + "(" + tfd.params.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + tfd.returnType + " is :\n" +
    " * Activating boolean : " + trActivatingBool + "\n" +
    " * Control booleans   : " + zippedCondVars.map(_._2.toString).mkString(", ") + "\n" +
    " * Expression vars    : " + zippedExprVars.map(_._2.toString).mkString(", ") + "\n" +
    " * Clauses            : " + "\n    " +trClauses.mkString("\n    ") + "\n" +
    " * Block-map          : " + trBlockers.toString
  }
}
