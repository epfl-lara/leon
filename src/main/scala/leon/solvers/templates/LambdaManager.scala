/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

class LambdaManager[T](encoder: TemplateEncoder[T]) {
  private type IdMap = Map[T, LambdaTemplate[T]]
  private var byIDStack : List[IdMap] = List(Map.empty)
  private def byID : IdMap = byIDStack.head
  private def byID_=(map: IdMap) : Unit = {
    byIDStack = map :: byIDStack.tail
  }

  private type TypeMap = Map[TypeTree, Set[(T, LambdaTemplate[T])]]
  private var byTypeStack : List[TypeMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def byType : TypeMap = byTypeStack.head
  private def byType_=(map: TypeMap) : Unit = {
    byTypeStack = map :: byTypeStack.tail
  }

  private type ApplicationMap = Map[TypeTree, Set[(T, App[T])]]
  private var applicationsStack : List[ApplicationMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def applications : ApplicationMap = applicationsStack.head
  private def applications_=(map: ApplicationMap) : Unit = {
    applicationsStack = map :: applicationsStack.tail
  }

  private type FreeMap = Map[TypeTree, Set[T]]
  private var freeLambdasStack : List[FreeMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def freeLambdas : FreeMap = freeLambdasStack.head
  private def freeLambdas_=(map: FreeMap) : Unit = {
    freeLambdasStack = map :: freeLambdasStack.tail
  }

  private type StructuralMap = Map[Lambda, List[(T, LambdaTemplate[T])]]
  private var structuralLambdasStack : List[StructuralMap] = List(Map.empty.withDefaultValue(List.empty))
  private def structuralLambdas : StructuralMap = structuralLambdasStack.head
  private def structuralLambdas_=(map: StructuralMap) : Unit = {
    structuralLambdasStack = map :: structuralLambdasStack.tail
  }

  def push(): Unit = {
    byIDStack = byID :: byIDStack
    byTypeStack = byType :: byTypeStack
    applicationsStack = applications :: applicationsStack
    freeLambdasStack = freeLambdas :: freeLambdasStack
    structuralLambdasStack = structuralLambdas :: structuralLambdasStack
  }

  def pop(lvl: Int): Unit = {
    byIDStack = byIDStack.drop(lvl)
    byTypeStack = byTypeStack.drop(lvl)
    applicationsStack = applicationsStack.drop(lvl)
    freeLambdasStack = freeLambdasStack.drop(lvl)
    structuralLambdasStack = structuralLambdasStack.drop(lvl)
  }

  def registerFree(lambdas: Seq[(TypeTree, T)]): Unit = {
    lambdas.foreach(p => freeLambdas += p._1 -> (freeLambdas(p._1) + p._2))
  }

  def instantiate(apps: Map[T, Set[App[T]]], lambdas: Map[T, LambdaTemplate[T]]) : (Seq[T], Map[T, Set[TemplateCallInfo[T]]], Map[(T, App[T]), Set[TemplateAppInfo[T]]]) = {
    var clauses : Seq[T] = Seq.empty
    var callBlockers : Map[T, Set[TemplateCallInfo[T]]] = Map.empty.withDefaultValue(Set.empty)
    var appBlockers  : Map[(T, App[T]), Set[TemplateAppInfo[T]]] = Map.empty.withDefaultValue(Set.empty)

    def mkBlocker(blockedApp: (T, App[T]), lambda: (T, LambdaTemplate[T])) : Unit = {
      val (_, App(caller, tpe, args)) = blockedApp
      val (idT, template) = lambda

      val equals = encoder.mkEquals(idT, caller)
      appBlockers += (blockedApp -> (appBlockers(blockedApp) + TemplateAppInfo(template, equals, args)))
    }

    for (lambda @ (idT, template) <- lambdas) {
      // get all lambda references...
      val lambdaRefs = freeLambdas(template.tpe) ++ byType(template.tpe).map(_._1)
      // ... and make sure the new lambda isn't equal to one of them!
      clauses ++= lambdaRefs.map(pIdT => encoder.mkNot(encoder.mkEquals(pIdT, idT)))

      byID += idT -> template
      byType += template.tpe -> (byType(template.tpe) + (idT -> template))

      for (guardedApp <- applications(template.tpe)) {
        mkBlocker(guardedApp, lambda)
      }
    }

    for ((b, fas) <- apps; app @ App(caller, tpe, args) <- fas) {
      if (byID contains caller) {
        val (newClauses, newCalls, newApps) = byID(caller).instantiate(b, args)

        clauses ++= newClauses
        newCalls.foreach(p => callBlockers += p._1 -> (callBlockers(p._1) ++ p._2))
        newApps.foreach(p => appBlockers += p._1 -> (appBlockers(p._1) ++ p._2))
      } else {
        val key = b -> app

        // make sure that even if byType(tpe) is empty, app is recorded in blockers
        // so that UnrollingBank will generate the initial block!
        if (!(appBlockers contains key)) appBlockers += key -> Set.empty

        for (lambda <- byType(tpe)) {
          mkBlocker(key, lambda)
        }

        applications += tpe -> (applications(tpe) + key)
      }
    }

    (clauses, callBlockers, appBlockers)
  }

  def equalityClauses(template: LambdaTemplate[T], idT: T, substMap: Map[T,T]): Seq[T] = {
    val key : Lambda = template.key
    val t : LambdaTemplate[T] = template.substitute(substMap)

    val newClauses = structuralLambdas(key).map { case (thatIdT, that) =>
      val equals = encoder.mkEquals(idT, thatIdT)
      if (t.dependencies.isEmpty) {
        equals
      } else {
        encoder.mkImplies(t.contextEquality(that), equals)
      }
    }

    structuralLambdas += key -> (structuralLambdas(key) :+ (idT -> t))

    newClauses
  }

}

