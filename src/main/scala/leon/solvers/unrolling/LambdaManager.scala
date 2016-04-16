/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package unrolling

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps.bestRealType

import utils._
import utils.SeqUtils._
import Instantiation._
import Template._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

case class App[T](caller: T, tpe: FunctionType, args: Seq[Arg[T]], encoded: T) {
  override def toString = "(" + caller + " : " + tpe + ")" + args.map(_.encoded).mkString("(", ",", ")")
  def substitute(substituter: T => T, msubst: Map[T, Matcher[T]]): App[T] = copy(
    caller = substituter(caller),
    args = args.map(_.substitute(substituter, msubst)),
    encoded = substituter(encoded)
  )
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
    val (clauses, blockers, applications, functions, matchers, templateString) =
      Template.encode(encoder, pathVar, arguments, condVars, exprVars, guardedExprs, lambdas, quantifications,
        substMap = baseSubstMap + ids, optApp = Some(id -> tpe))

    assert(functions.isEmpty, "Only synthetic type explorers should introduce functions!")

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
      lambdas,
      matchers,
      quantifications,
      keyDeps,
      key -> structSubst,
      lambdaString
    )
  }
}

trait KeyedTemplate[T, E <: Expr] {
  val dependencies: Map[Identifier, T]
  val structure: E

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

    structure -> rec(structure).distinct.map(dependencies)
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
  val lambdas: Seq[LambdaTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val quantifications: Seq[QuantificationTemplate[T]],
  val dependencies: Map[Identifier, T],
  val struct: (Lambda, Map[Identifier, Identifier]),
  stringRepr: () => String) extends Template[T] with KeyedTemplate[T, Lambda] {

  val args = arguments.map(_._2)
  val tpe = bestRealType(ids._1.getType).asInstanceOf[FunctionType]
  val functions: Set[(T, FunctionType, T)] = Set.empty
  val (structure, structSubst) = struct

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

    val newLambdas = lambdas.map(_.substitute(substituter, matcherSubst))

    val newMatchers = matchers.map { case (b, ms) =>
      val bp = if (b == start) newStart else b
      bp -> ms.map(_.substitute(substituter, matcherSubst))
    }

    val newQuantifications = quantifications.map(_.substitute(substituter, matcherSubst))

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
      newLambdas,
      newMatchers,
      newQuantifications,
      newDependencies,
      struct,
      stringRepr
    )
  }

  def withId(idT: T): LambdaTemplate[T] = {
    val substituter = encoder.substitute(Map(ids._2 -> idT))
    new LambdaTemplate[T](
      ids._1 -> idT, encoder, manager, pathVar, arguments, condVars, exprVars, condTree,
      clauses map substituter, // make sure the body-defining clause is inlined!
      blockers, applications, lambdas, matchers, quantifications,
      dependencies, struct, stringRepr
    )
  }

  private lazy val str : String = stringRepr()
  override def toString : String = str

  override def instantiate(substMap: Map[T, Arg[T]]): Instantiation[T] = {
    super.instantiate(substMap) ++ manager.instantiateAxiom(this, substMap)
  }
}

class LambdaManager[T](encoder: TemplateEncoder[T]) extends DatatypeManager(encoder) {
  private[unrolling] lazy val trueT = encoder.encodeExpr(Map.empty)(BooleanLiteral(true))

  protected[unrolling] val byID = new IncrementalMap[T, LambdaTemplate[T]]
  protected val byType          = new IncrementalMap[FunctionType, Map[(Expr, Seq[T]), LambdaTemplate[T]]].withDefaultValue(Map.empty)
  protected val applications    = new IncrementalMap[FunctionType, Set[(T, App[T])]].withDefaultValue(Set.empty)
  protected val knownFree       = new IncrementalMap[FunctionType, Set[T]].withDefaultValue(Set.empty)
  protected val maybeFree       = new IncrementalMap[FunctionType, Set[(T, T)]].withDefaultValue(Set.empty)
  protected val freeBlockers    = new IncrementalMap[FunctionType, Set[(T, T)]].withDefaultValue(Set.empty)

  private val instantiated = new IncrementalSet[(T, App[T])]

  override protected def incrementals: List[IncrementalState] =
    super.incrementals ++ List(byID, byType, applications, knownFree, maybeFree, freeBlockers, instantiated)

  def registerFunction(b: T, tpe: FunctionType, f: T): Instantiation[T] = {
    val ft = bestRealType(tpe).asInstanceOf[FunctionType]
    val bs = fixpoint((bs: Set[T]) => bs ++ bs.flatMap(blockerParents))(Set(b))

    val (known, neqClauses) = if ((bs intersect typeEnablers).nonEmpty) {
      maybeFree += ft -> (maybeFree(ft) + (b -> f))
      (false, byType(ft).values.toSeq.map { t =>
        encoder.mkImplies(b, encoder.mkNot(encoder.mkEquals(t.ids._2, f)))
      })
    } else {
      knownFree += ft -> (knownFree(ft) + f)
      (true, byType(ft).values.toSeq.map(t => encoder.mkNot(encoder.mkEquals(t.ids._2, f))))
    }

    val extClauses = freeBlockers(tpe).map { case (oldB, freeF) =>
      val equals = encoder.mkEquals(f, freeF)
      val nextB  = encoder.encodeId(FreshIdentifier("b_or", BooleanType, true))
      val extension = encoder.mkOr(if (known) equals else encoder.mkAnd(b, equals), nextB)
      encoder.mkEquals(oldB, extension)
    }

    val instantiation = Instantiation.empty[T] withClauses (neqClauses ++ extClauses)

    applications(tpe).foldLeft(instantiation) {
      case (instantiation, (app @ (_, App(caller, _, args, _)))) =>
        val equals = encoder.mkAnd(b, encoder.mkEquals(f, caller))
        instantiation withApp (app -> TemplateAppInfo(f, equals, args))
    }
  }

  def assumptions: Seq[T] = freeBlockers.toSeq.flatMap(_._2.map(p => encoder.mkNot(p._1)))

  private val typeBlockers = new IncrementalMap[T, T]()
  private val typeEnablers: MutableSet[T] = MutableSet.empty

  private def typeUnroller(blocker: T, app: App[T]): Instantiation[T] = typeBlockers.get(app.encoded) match {
    case Some(typeBlocker) =>
      implies(blocker, typeBlocker)
      (Seq(encoder.mkImplies(blocker, typeBlocker)), Map.empty, Map.empty)

    case None =>
      val App(caller, tpe @ FirstOrderFunctionType(_, to), args, value) = app
      val typeBlocker = encoder.encodeId(FreshIdentifier("t", BooleanType))
      typeBlockers += value -> typeBlocker
      implies(blocker, typeBlocker)

      val template = typeTemplate(to)
      val instantiation = template.instantiate(typeBlocker, value)

      val (b, extClauses) = if (knownFree(tpe) contains caller) {
        (blocker, Seq.empty)
      } else {
        val firstB = encoder.encodeId(FreshIdentifier("b_free", BooleanType, true))
        implies(firstB, typeBlocker)
        typeEnablers += firstB

        val nextB  = encoder.encodeId(FreshIdentifier("b_or", BooleanType, true))
        freeBlockers += tpe -> (freeBlockers(tpe) + (nextB -> caller))

        val clause = encoder.mkEquals(firstB, encoder.mkAnd(blocker, encoder.mkOr(
          knownFree(tpe).map(idT => encoder.mkEquals(caller, idT)).toSeq ++
          maybeFree(tpe).map { case (b, idT) => encoder.mkAnd(b, encoder.mkEquals(caller, idT)) } :+
          nextB : _*)))
        (firstB, Seq(clause))
      }

      instantiation withClauses extClauses withClause encoder.mkImplies(b, typeBlocker)
  }

  def instantiateLambda(template: LambdaTemplate[T]): (T, Instantiation[T]) = {
    byType(template.tpe).get(template.key) match {
      case Some(template) =>
        (template.ids._2, Instantiation.empty)

      case None =>
        val idT = encoder.encodeId(template.ids._1)
        val newTemplate = template.withId(idT)

        // make sure the new lambda isn't equal to any free lambda var
        val instantiation = Instantiation.empty[T] withClauses (
          equalityClauses(newTemplate) ++
          knownFree(newTemplate.tpe).map(f => encoder.mkNot(encoder.mkEquals(idT, f))).toSeq ++
          maybeFree(newTemplate.tpe).map { p =>
            encoder.mkImplies(p._1, encoder.mkNot(encoder.mkEquals(idT, p._2)))
          })

        byID += idT -> newTemplate
        byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.key -> newTemplate))

        val inst = applications(newTemplate.tpe).foldLeft(instantiation) {
          case (instantiation, app @ (_, App(caller, _, args, _))) =>
            val equals = encoder.mkEquals(idT, caller)
            instantiation withApp (app -> TemplateAppInfo(newTemplate, equals, args))
        }

        (idT, inst)
    }
  }

  def instantiateApp(blocker: T, app: App[T]): Instantiation[T] = {
    val App(caller, tpe @ FunctionType(_, to), args, encoded) = app

    val instantiation: Instantiation[T] = if (byID contains caller) {
      Instantiation.empty
    } else {
      typeUnroller(blocker, app)
    }

    val key = blocker -> app
    if (instantiated(key)) {
      instantiation
    } else {
      instantiated += key

      if (knownFree(tpe) contains caller) {
        instantiation
      } else if (byID contains caller) {
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

