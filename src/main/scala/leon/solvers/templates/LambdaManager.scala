/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import Instantiation._

class LambdaManager[T](protected val encoder: TemplateEncoder[T]) {

  protected type IdMap = Map[T, LambdaTemplate[T]]
  protected def byID : IdMap = byIDStack.head
  private var byIDStack : List[IdMap] = List(Map.empty)
  private def byID_=(map: IdMap) : Unit = {
    byIDStack = map :: byIDStack.tail
  }

  protected type TypeMap = Map[FunctionType, Set[(T, LambdaTemplate[T])]]
  protected def byType : TypeMap = byTypeStack.head
  private var byTypeStack : List[TypeMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def byType_=(map: TypeMap) : Unit = {
    byTypeStack = map :: byTypeStack.tail
  }

  protected type ApplicationMap = Map[FunctionType, Set[(T, App[T])]]
  protected def applications : ApplicationMap = applicationsStack.head
  private var applicationsStack : List[ApplicationMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def applications_=(map: ApplicationMap) : Unit = {
    applicationsStack = map :: applicationsStack.tail
  }

  protected type FreeMap = Map[FunctionType, Set[T]]
  protected def freeLambdas : FreeMap = freeLambdasStack.head
  private var freeLambdasStack : List[FreeMap] = List(Map.empty.withDefaultValue(Set.empty))
  private def freeLambdas_=(map: FreeMap) : Unit = {
    freeLambdasStack = map :: freeLambdasStack.tail
  }

  def push(): Unit = {
    byIDStack = byID :: byIDStack
    byTypeStack = byType :: byTypeStack
    applicationsStack = applications :: applicationsStack
    freeLambdasStack = freeLambdas :: freeLambdasStack
  }

  def pop(lvl: Int): Unit = {
    byIDStack = byIDStack.drop(lvl)
    byTypeStack = byTypeStack.drop(lvl)
    applicationsStack = applicationsStack.drop(lvl)
    freeLambdasStack = freeLambdasStack.drop(lvl)
  }

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

