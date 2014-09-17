/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

class LambdaManager[T](encoder: TemplateEncoder[T]) {
  private var byID : Map[T, LambdaTemplate[T]] = Map.empty
  private var byType : Map[TypeTree, Set[(T, LambdaTemplate[T])]] = Map.empty.withDefaultValue(Set.empty)
  private var quantified : Map[TypeTree, Set[T]] = Map.empty.withDefaultValue(Set.empty)
  private var applications : Map[TypeTree, Set[(T, App[T])]] = Map.empty.withDefaultValue(Set.empty)
  private var blockedApplications : Map[(T, App[T]), Set[T]] = Map.empty.withDefaultValue(Set.empty)

  private var globalBlocker : Option[T] = None
  private var previousGlobals : Set[T] = Set.empty

  def quantify(args: Seq[(TypeTree, T)]): Unit = {
    args.foreach(p => quantified += p._1 -> (quantified(p._1) + p._2))
  }

  def instantiate(apps: Map[T, Set[App[T]]], lambdas: Map[T, LambdaTemplate[T]]) : (Seq[T], Map[T, Set[TemplateInfo[T]]]) = {
    var clauses : Seq[T] = Seq.empty
    var blockers : Map[T, Set[TemplateInfo[T]]] = Map.empty.withDefaultValue(Set.empty)

    def mkBlocker(blockedApp: (T, App[T]), lambda: (T, LambdaTemplate[T])) : Unit = {
      val (_, App(caller, tpe, args)) = blockedApp
      val (idT, template) = lambda

      val unrollingBlocker = encoder.encodeId(FreshIdentifier("unrolled", true).setType(BooleanType))

      val conj = encoder.mkAnd(encoder.mkEquals(idT, caller), template.start, unrollingBlocker)

      val templateBlocker = encoder.encodeId(FreshIdentifier("b", true).setType(BooleanType))
      val constraint = encoder.mkEquals(templateBlocker, conj)

      clauses :+= constraint
      blockedApplications += (blockedApp -> (blockedApplications(blockedApp) + templateBlocker))
      blockers += (unrollingBlocker -> Set(TemplateAppInfo(template, templateBlocker, args)))
    }

    for (lambda @ (idT, template) <- lambdas) {
      byID += idT -> template
      byType += template.tpe -> (byType(template.tpe) + (idT -> template))

      for (guardedApp <- applications(template.tpe)) {
        mkBlocker(guardedApp, lambda)
      }
    }

    for ((b, fas) <- apps; app @ App(caller, tpe, args) <- fas) {
      if (byID contains caller) {
        val (newClauses, newBlockers) = byID(caller).instantiate(b, args)
        clauses ++= newClauses
        newBlockers.foreach(p => blockers += p._1 -> (blockers(p._1) ++ p._2))
      } else {
        for (lambda <- byType(tpe)) {
          mkBlocker(b -> app, lambda)
        }

        applications += tpe -> (applications(tpe) + (b -> app))
      }
    }

    (clauses, blockers)
  }

  def guards : Seq[T] = {
    previousGlobals ++= globalBlocker
    val globalGuard = encoder.encodeId(FreshIdentifier("lambda_phaser", true).setType(BooleanType))
    globalBlocker = Some(globalGuard)

    (for (((b, App(caller, tpe, _)), tbs) <- blockedApplications) yield {
      val qbs = quantified(tpe).map(l => encoder.mkEquals(caller, l))
      val or = encoder.mkOr((tbs ++ qbs).toSeq : _*)
      // TODO: get global blocker
      val guard = encoder.mkAnd(globalGuard, encoder.mkNot(or))
      encoder.mkImplies(guard, encoder.mkNot(b))
    }).toSeq ++ previousGlobals.map(encoder.mkNot(_))
  }

  def assumption : T = globalBlocker.get
}

