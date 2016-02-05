/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

import utils._
import Instantiation._
import Template._

case class App[T](caller: T, tpe: FunctionType, args: Seq[Arg[T]]) {
  override def toString = "(" + caller + " : " + tpe + ")" + args.map(_.encoded).mkString("(", ",", ")")
}

object LambdaTemplate {

  def apply[T](
    ids: (Identifier, T),
    encoder: TemplateEncoder[T],
    manager: QuantificationManager[T],
    pathVar: (Identifier, T),
    arguments: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    condTree: Map[Identifier, Set[Identifier]],
    guardedExprs: Map[Identifier, Seq[Expr]],
    quantifications: Seq[QuantificationTemplate[T]],
    lambdas: Seq[LambdaTemplate[T]],
    baseSubstMap: Map[Identifier, T],
    dependencies: Map[Identifier, T],
    lambda: Lambda
  ) : LambdaTemplate[T] = {

    val id = ids._2
    val tpe = ids._1.getType.asInstanceOf[FunctionType]
    val (clauses, blockers, applications, matchers, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas,
        substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

    val lambdaString : () => String = () => {
      "Template for lambda " + ids._1 + ": " + lambda + " is :\n" + templateString()
    }

    val (structuralLambda, structSubst) = normalizeStructure(lambda)
    val keyDeps = dependencies.map { case (id, idT) => structSubst(id) -> idT }
    val key = structuralLambda.asInstanceOf[Lambda]

    new LambdaTemplate[T](
      ids,
      encoder,
      manager,
      pathVar,
      arguments,
      condVars,
      exprVars,
      condTree,
      clauses,
      blockers,
      applications,
      quantifications,
      matchers,
      lambdas,
      keyDeps,
      key,
      lambdaString
    )
  }
}

trait KeyedTemplate[T, E <: Expr] {
  val dependencies: Map[Identifier, T]
  val structuralKey: E

  lazy val key: (E, Seq[T]) = {
    def rec(e: Expr): Seq[Identifier] = e match {
      case Variable(id) =>
        if (dependencies.isDefinedAt(id)) {
          Seq(id)
        } else {
          Seq.empty
        }

      case Operator(es, _) => es.flatMap(rec)

      case _ => Seq.empty
    }

    structuralKey -> rec(structuralKey).distinct.map(dependencies)
  }
}

class LambdaTemplate[T] private (
  val ids: (Identifier, T),
  val encoder: TemplateEncoder[T],
  val manager: QuantificationManager[T],
  val pathVar: (Identifier, T),
  val arguments: Seq[(Identifier, T)],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val condTree: Map[Identifier, Set[Identifier]],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val quantifications: Seq[QuantificationTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Seq[LambdaTemplate[T]],
  val dependencies: Map[Identifier, T],
  val structuralKey: Lambda,
  stringRepr: () => String) extends Template[T] with KeyedTemplate[T, Lambda] {

  val args = arguments.map(_._2)
  val tpe = ids._1.getType.asInstanceOf[FunctionType]

  def substitute(substituter: T => T, matcherSubst: Map[T, Matcher[T]]): LambdaTemplate[T] = {
    val newStart = substituter(start)
    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b, fis) =>
      val bp = if (b == start) newStart else b
      bp -> fis.map(fi => fi.copy(
        args = fi.args.map(_.substitute(substituter, matcherSubst))
      ))
    }

    val newApplications = applications.map { case (b, fas) =>
      val bp = if (b == start) newStart else b
      bp -> fas.map(fa => fa.copy(
        caller = substituter(fa.caller),
        args = fa.args.map(_.substitute(substituter, matcherSubst))
      ))
    }

    val newQuantifications = quantifications.map(_.substitute(substituter, matcherSubst))

    val newMatchers = matchers.map { case (b, ms) =>
      val bp = if (b == start) newStart else b
      bp -> ms.map(_.substitute(substituter, matcherSubst))
    }

    val newLambdas = lambdas.map(_.substitute(substituter, matcherSubst))

    val newDependencies = dependencies.map(p => p._1 -> substituter(p._2))

    new LambdaTemplate[T](
      ids._1 -> substituter(ids._2),
      encoder,
      manager,
      pathVar._1 -> newStart,
      arguments,
      condVars,
      exprVars,
      condTree,
      newClauses,
      newBlockers,
      newApplications,
      newQuantifications,
      newMatchers,
      newLambdas,
      newDependencies,
      structuralKey,
      stringRepr
    )
  }

  def withId(idT: T): LambdaTemplate[T] = {
    val substituter = encoder.substitute(Map(ids._2 -> idT))
    new LambdaTemplate[T](
      ids._1 -> idT, encoder, manager, pathVar, arguments, condVars, exprVars, condTree,
      clauses map substituter, // make sure the body-defining clause is inlined!
      blockers, applications, quantifications, matchers, lambdas,
      dependencies, structuralKey, stringRepr
    )
  }

  private lazy val str : String = stringRepr()
  override def toString : String = str

  override def instantiate(substMap: Map[T, Arg[T]]): Instantiation[T] = {
    super.instantiate(substMap) ++ manager.instantiateAxiom(this, substMap)
  }
}

class LambdaManager[T](encoder: TemplateEncoder[T]) extends TemplateManager(encoder) {
  private[templates] lazy val trueT = encoder.encodeExpr(Map.empty)(BooleanLiteral(true))

  protected[templates] val byID = new IncrementalMap[T, LambdaTemplate[T]]
  protected val byType          = new IncrementalMap[FunctionType, Map[(Expr, Seq[T]), LambdaTemplate[T]]].withDefaultValue(Map.empty)
  protected val applications    = new IncrementalMap[FunctionType, Set[(T, App[T])]].withDefaultValue(Set.empty)
  protected val freeLambdas     = new IncrementalMap[FunctionType, Set[T]].withDefaultValue(Set.empty)

  private val instantiated = new IncrementalSet[(T, App[T])]

  override protected def incrementals: List[IncrementalState] =
    super.incrementals ++ List(byID, byType, applications, freeLambdas, instantiated)

  def registerFree(lambdas: Seq[(Identifier, T)]): Unit = {
    for ((id, idT) <- lambdas) id.getType match {
      case ft: FunctionType =>
        freeLambdas += ft -> (freeLambdas(ft) + idT)
      case _ =>
    }
  }

  def instantiateLambda(template: LambdaTemplate[T]): (T, Instantiation[T]) = {
    byType(template.tpe).get(template.key) match {
      case Some(template) =>
        (template.ids._2, Instantiation.empty)

      case None =>
        val idT = encoder.encodeId(template.ids._1)
        val newTemplate = template.withId(idT)

        var clauses      : Clauses[T]     = equalityClauses(newTemplate)
        var appBlockers  : AppBlockers[T] = Map.empty.withDefaultValue(Set.empty)

        // make sure the new lambda isn't equal to any free lambda var
        clauses ++= freeLambdas(newTemplate.tpe).map(pIdT => encoder.mkNot(encoder.mkEquals(idT, pIdT)))

        byID += idT -> newTemplate
        byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.key -> newTemplate))

        for (blockedApp @ (_, App(caller, tpe, args)) <- applications(newTemplate.tpe)) {
          val equals = encoder.mkEquals(idT, caller)
          appBlockers += (blockedApp -> (appBlockers(blockedApp) + TemplateAppInfo(newTemplate, equals, args)))
        }

        (idT, (clauses, Map.empty, appBlockers))
    }
  }

  def instantiateApp(blocker: T, app: App[T]): Instantiation[T] = {
    val App(caller, tpe, args) = app
    val instantiation = Instantiation.empty[T]

    if (freeLambdas(tpe).contains(caller)) instantiation else {
      val key = blocker -> app

      if (instantiated(key)) instantiation else {
        instantiated += key

        if (byID contains caller) {
          instantiation withApp (key -> TemplateAppInfo(byID(caller), trueT, args))
        } else {

          // make sure that even if byType(tpe) is empty, app is recorded in blockers
          // so that UnrollingBank will generate the initial block!
          val init = instantiation withApps Map(key -> Set.empty)
          val inst = byType(tpe).values.foldLeft(init) {
            case (instantiation, template) =>
              val equals = encoder.mkEquals(template.ids._2, caller)
              instantiation withApp (key -> TemplateAppInfo(template, equals, args))
          }

          applications += tpe -> (applications(tpe) + key)

          inst
        }
      }
    }
  }

  private def equalityClauses(template: LambdaTemplate[T]): Seq[T] = {
    val (s1, deps1) = template.key
    byType(template.tpe).values.map { that =>
      val (s2, deps2) = that.key
      val equals = encoder.mkEquals(template.ids._2, that.ids._2)
      if (s1 == s2) {
        val pairs = (deps1 zip deps2).filter(p => p._1 != p._2)
        if (pairs.isEmpty) equals else {
          val eqs = pairs.map(p => encoder.mkEquals(p._1, p._2))
          encoder.mkEquals(encoder.mkAnd(eqs : _*), equals)
        }
      } else {
        encoder.mkNot(equals)
      }
    }.toSeq
  }
}

