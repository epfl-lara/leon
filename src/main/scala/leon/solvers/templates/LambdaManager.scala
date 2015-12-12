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

case class App[T](caller: T, tpe: FunctionType, args: Seq[T]) {
  override def toString = "(" + caller + " : " + tpe + ")" + args.mkString("(", ",", ")")
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
  private[templates] val dependencies: Map[Identifier, T],
  private[templates] val structuralKey: Lambda,
  stringRepr: () => String) extends Template[T] {

  val args = arguments.map(_._2)
  val tpe = ids._1.getType.asInstanceOf[FunctionType]

  def substitute(substituter: T => T): LambdaTemplate[T] = {
    val newStart = substituter(start)
    val newClauses = clauses.map(substituter)
    val newBlockers = blockers.map { case (b, fis) =>
      val bp = if (b == start) newStart else b
      bp -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
    }

    val newApplications = applications.map { case (b, fas) =>
      val bp = if (b == start) newStart else b
      bp -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
    }

    val newQuantifications = quantifications.map(_.substitute(substituter))

    val newMatchers = matchers.map { case (b, ms) =>
      val bp = if (b == start) newStart else b
      bp -> ms.map(_.substitute(substituter))
    }

    val newLambdas = lambdas.map(_.substitute(substituter))

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

  private lazy val str : String = stringRepr()
  override def toString : String = str

  lazy val key: (Expr, Seq[T]) = {
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

  override def equals(that: Any): Boolean = that match {
    case t: LambdaTemplate[T] =>
      val (lambda1, deps1) = key
      val (lambda2, deps2) = t.key
      (lambda1 == lambda2) && {
        (deps1 zip deps2).forall { case (id1, id2) =>
          (manager.byID.get(id1), manager.byID.get(id2)) match {
            case (Some(t1), Some(t2)) => t1 == t2
            case _ => id1 == id2
          }
        }
      }

    case _ => false
  }

  override def hashCode: Int = key.hashCode

  override def instantiate(substMap: Map[T, T]): Instantiation[T] = {
    super.instantiate(substMap) ++ manager.instantiateAxiom(this, substMap)
  }
}

class LambdaManager[T](encoder: TemplateEncoder[T]) extends TemplateManager(encoder) {
  private[templates] lazy val trueT = encoder.encodeExpr(Map.empty)(BooleanLiteral(true))

  protected[templates] val byID = new IncrementalMap[T, LambdaTemplate[T]]
  protected val byType          = new IncrementalMap[FunctionType, Set[LambdaTemplate[T]]].withDefaultValue(Set.empty)
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

  def instantiateLambda(template: LambdaTemplate[T]): Instantiation[T] = {
    val idT = template.ids._2
    var clauses      : Clauses[T]     = equalityClauses(template)
    var appBlockers  : AppBlockers[T] = Map.empty.withDefaultValue(Set.empty)

    // make sure the new lambda isn't equal to any free lambda var
    clauses ++= freeLambdas(template.tpe).map(pIdT => encoder.mkNot(encoder.mkEquals(pIdT, idT)))

    byID += idT -> template

    if (byType(template.tpe)(template)) {
      (clauses, Map.empty, Map.empty)
    } else {
      byType += template.tpe -> (byType(template.tpe) + template)

      for (blockedApp @ (_, App(caller, tpe, args)) <- applications(template.tpe)) {
        val equals = encoder.mkEquals(idT, caller)
        appBlockers += (blockedApp -> (appBlockers(blockedApp) + TemplateAppInfo(template, equals, args)))
      }

      (clauses, Map.empty, appBlockers)
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
          val inst = byType(tpe).foldLeft(init) {
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
    byType(template.tpe).map { that =>
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

