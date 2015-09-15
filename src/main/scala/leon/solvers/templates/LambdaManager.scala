/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import utils._
import Instantiation._

class LambdaManager[T](protected val encoder: TemplateEncoder[T]) extends IncrementalState {

  protected val byID         = new IncrementalMap[T, LambdaTemplate[T]]
  protected val byType       = new IncrementalMap[FunctionType, Set[(T, LambdaTemplate[T])]].withDefaultValue(Set.empty)
  protected val applications = new IncrementalMap[FunctionType, Set[(T, App[T])]].withDefaultValue(Set.empty)
  protected val freeLambdas  = new IncrementalMap[FunctionType, Set[T]].withDefaultValue(Set.empty)

  protected def incrementals: List[IncrementalState] =
    List(byID, byType, applications, freeLambdas)

  def clear(): Unit = incrementals.foreach(_.clear())
  def reset(): Unit = incrementals.foreach(_.reset())
  def push(): Unit = incrementals.foreach(_.push())
  def pop(): Unit = incrementals.foreach(_.pop())

  def registerFree(lambdas: Seq[(TypeTree, T)]): Unit = {
    for ((tpe, idT) <- lambdas) tpe match {
      case ft: FunctionType =>
        freeLambdas += ft -> (freeLambdas(ft) + idT)
      case _ =>
    }
  }

  def instantiateLambda(idT: T, template: LambdaTemplate[T]): Instantiation[T] = {
    var clauses      : Clauses[T]     = equalityClauses(idT, template)
    var appBlockers  : AppBlockers[T] = Map.empty.withDefaultValue(Set.empty)

    // make sure the new lambda isn't equal to any free lambda var
    clauses ++= freeLambdas(template.tpe).map(pIdT => encoder.mkNot(encoder.mkEquals(pIdT, idT)))

    byID += idT -> template
    byType += template.tpe -> (byType(template.tpe) + (idT -> template))

    for (blockedApp @ (_, App(caller, tpe, args)) <- applications(template.tpe)) {
      val equals = encoder.mkEquals(idT, caller)
      appBlockers += (blockedApp -> (appBlockers(blockedApp) + TemplateAppInfo(template, equals, args)))
    }

    (clauses, Map.empty, appBlockers)
  }

  def instantiateApp(blocker: T, app: App[T]): Instantiation[T] = {
    val App(caller, tpe, args) = app
    var clauses      : Clauses[T]      = Seq.empty
    var callBlockers : CallBlockers[T] = Map.empty.withDefaultValue(Set.empty)
    var appBlockers  : AppBlockers[T]  = Map.empty.withDefaultValue(Set.empty)

    if (byID contains caller) {
      val (newClauses, newCalls, newApps) = byID(caller).instantiate(blocker, args)

      clauses ++= newClauses
      newCalls.foreach(p => callBlockers += p._1 -> (callBlockers(p._1) ++ p._2))
      newApps.foreach(p => appBlockers += p._1 -> (appBlockers(p._1) ++ p._2))
    } else if (!freeLambdas(tpe).contains(caller)) {
      val key = blocker -> app

      // make sure that even if byType(tpe) is empty, app is recorded in blockers
      // so that UnrollingBank will generate the initial block!
      if (!(appBlockers contains key)) appBlockers += key -> Set.empty

      for ((idT,template) <- byType(tpe)) {
        val equals = encoder.mkEquals(idT, caller)
        appBlockers += (key -> (appBlockers(key) + TemplateAppInfo(template, equals, args)))
      }

      applications += tpe -> (applications(tpe) + key)
    }

    (clauses, callBlockers, appBlockers)
  }

  private def equalityClauses(idT: T, template: LambdaTemplate[T]): Seq[T] = {
    byType(template.tpe).map { case (thatIdT, that) =>
      val equals = encoder.mkEquals(idT, thatIdT)
      template.contextEquality(that) match {
        case None => encoder.mkNot(equals)
        case Some(Seq()) => equals
        case Some(seq) => encoder.mkEquals(encoder.mkAnd(seq : _*), equals)
      }
    }.toSeq
  }

}

