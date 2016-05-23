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

/** Represents an application of a first-class function in the unfolding procedure */
case class App[T](caller: T, tpe: FunctionType, args: Seq[Arg[T]], encoded: T) {
  override def toString = "(" + caller + " : " + tpe + ")" + args.map(_.encoded).mkString("(", ",", ")")
  def substitute(substituter: T => T, msubst: Map[T, Matcher[T]]): App[T] = copy(
    caller = substituter(caller),
    args = args.map(_.substitute(substituter, msubst)),
    encoded = substituter(encoded)
  )
}

/** Constructor object for [[LambdaTemplate]]
  *
  * The [[apply]] methods performs some pre-processing before creating
  * an instance of [[LambdaTemplate]].
  */
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
    structure: LambdaStructure[T],
    baseSubstMap: Map[Identifier, T],
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
      structure,
      lambda,
      lambdaString
    )
  }
}

/** Semi-template used for hardcore function equality
  *
  * Function equality, while unhandled in general, can be very useful for certain
  * proofs that refer specifically to first-class functions. In order to support
  * such proofs, flexible notions of equality on first-class functions are
  * necessary. These are provided by [[LambdaStructure]] which, much like a
  * [[Template]], will generate clauses that represent equality between two
  * functions.
  *
  * To support complex cases of equality where closed portions of the first-class
  * function rely on complex program features (function calls, introducing lambdas,
  * foralls, etc.), we use a structure that resembles a [[Template]] that is
  * instantiated when function equality is of interest.
  *
  * Note that lambda creation now introduces clauses to determine equality between
  * closed portions (that are independent of the lambda arguments).
  */
class LambdaStructure[T] private[unrolling] (
  /** @see [[Template.encoder]] */
  val encoder: TemplateEncoder[T],
  /** @see [[Template.manager]] */
  val manager: QuantificationManager[T],

  /** The normalized lambda that is shared between all "equal" first-class functions.
    * First-class function equality is conditionned on `lambda` equality.
    *
    * @see [[dependencies]] for the other component of equality between first-class functions
    */
  val lambda: Lambda,

  /** The closed expressions (independent of the arguments to [[lambda]] contained in
    * the first-class function. Equality is conditioned on equality of `dependencies`
    * (inside the solver).
    *
    * @see [[lambda]] for the other component of equality between first-class functions
    */
  val dependencies: Seq[T],
  val pathVar: (Identifier, T),

  /** The set of closed variables that exist in the associated lambda.
    *
    * This set is necessary to determine whether other closures have been
    * captured by this particular closure when deciding the order of
    * lambda instantiations in [[Template.substitution]].
    */
  val closures: Seq[T],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val condTree: Map[Identifier, Set[Identifier]],
  val clauses: Seq[T],
  val blockers: Calls[T],
  val applications: Apps[T],
  val lambdas: Seq[LambdaTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val quantifications: Seq[QuantificationTemplate[T]]) {

  def substitute(substituter: T => T, matcherSubst: Map[T, Matcher[T]]) = new LambdaStructure[T](
    encoder, manager, lambda,
    dependencies.map(substituter),
    pathVar._1 -> substituter(pathVar._2),
    closures.map(substituter), condVars, exprVars, condTree,
    clauses.map(substituter),
    blockers.map { case (b, fis) => substituter(b) -> fis.map(fi => fi.copy(
      args = fi.args.map(_.substitute(substituter, matcherSubst)))) },
    applications.map { case (b, fas) => substituter(b) -> fas.map(_.substitute(substituter, matcherSubst)) },
    lambdas.map(_.substitute(substituter, matcherSubst)),
    matchers.map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter, matcherSubst)) },
    quantifications.map(_.substitute(substituter, matcherSubst)))

  /** The [[key]] value (tuple of [[lambda]] and [[dependencies]]) is used
    * to determine syntactic equality between lambdas. If the keys of two
    * closures are equal, then they must necessarily be equal in every model.
    *
    * The [[instantiation]] consists of the clause set instantiation (in the
    * sense of [[Template.instantiate]] that is required for [[dependencies]]
    * to make sense in the solver (introduces blockers, quantifications, other
    * lambdas, etc.) Since [[dependencies]] CHANGE during instantiation and
    * [[key]] makes no sense without the associated instantiation, the implicit
    * contract here is that whenever a new key appears during unfolding, its
    * associated instantiation MUST be added to the set of instantiations
    * managed by the solver. However, if an identical pre-existing key has
    * already been found, then the associated instantiations must already appear
    * in those handled by the solver.
    */
  lazy val (key, instantiation) = {
    val (substMap, substInst) = Template.substitution[T](encoder, manager,
      condVars, exprVars, condTree, quantifications, lambdas, Set.empty, Map.empty, pathVar._1, pathVar._2)
    val tmplInst = Template.instantiate(encoder, manager, clauses, blockers, applications, matchers, substMap)

    val key = (lambda, dependencies.map(encoder.substitute(substMap.mapValues(_.encoded))))
    val instantiation = substInst ++ tmplInst
    (key, instantiation)
  }

  override def equals(that: Any): Boolean = that match {
    case (struct: LambdaStructure[T]) => key == struct.key
    case _ => false
  }

  override def hashCode: Int = key.hashCode
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
  val clauses: Clauses[T],
  val blockers: Calls[T],
  val applications: Apps[T],
  val lambdas: Seq[LambdaTemplate[T]],
  val matchers: Map[T, Set[Matcher[T]]],
  val quantifications: Seq[QuantificationTemplate[T]],
  val structure: LambdaStructure[T],
  val lambda: Lambda,
  stringRepr: () => String) extends Template[T] {

  val args = arguments.map(_._2)
  val tpe = bestRealType(ids._1.getType).asInstanceOf[FunctionType]
  val functions: Set[(T, FunctionType, T)] = Set.empty

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
      bp -> fas.map(_.substitute(substituter, matcherSubst))
    }

    val newLambdas = lambdas.map(_.substitute(substituter, matcherSubst))

    val newMatchers = matchers.map { case (b, ms) =>
      val bp = if (b == start) newStart else b
      bp -> ms.map(_.substitute(substituter, matcherSubst))
    }

    val newQuantifications = quantifications.map(_.substitute(substituter, matcherSubst))

    val newStructure = structure.substitute(substituter, matcherSubst)

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
      newStructure,
      lambda,
      stringRepr
    )
  }

  def withId(idT: T): LambdaTemplate[T] = {
    val substituter = encoder.substitute(Map(ids._2 -> idT))
    new LambdaTemplate[T](
      ids._1 -> idT, encoder, manager, pathVar, arguments, condVars, exprVars, condTree,
      clauses map substituter, // make sure the body-defining clause is inlined!
      blockers, applications, lambdas, matchers, quantifications,
      structure, lambda, stringRepr
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
  protected val byType          = new IncrementalMap[FunctionType, Map[LambdaStructure[T], LambdaTemplate[T]]].withDefaultValue(Map.empty)
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
    byType(template.tpe).get(template.structure) match {
      case Some(template) =>
        (template.ids._2, Instantiation.empty)

      case None =>
        val idT = encoder.encodeId(template.ids._1)
        val newTemplate = template.withId(idT)

        // make sure the new lambda isn't equal to any free lambda var
        val instantiation = newTemplate.structure.instantiation withClauses (
          equalityClauses(newTemplate) ++
          knownFree(newTemplate.tpe).map(f => encoder.mkNot(encoder.mkEquals(idT, f))).toSeq ++
          maybeFree(newTemplate.tpe).map { p =>
            encoder.mkImplies(p._1, encoder.mkNot(encoder.mkEquals(idT, p._2)))
          })

        byID += idT -> newTemplate
        byType += newTemplate.tpe -> (byType(newTemplate.tpe) + (newTemplate.structure -> newTemplate))

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
    byType(template.tpe).values.map { that =>
      val equals = encoder.mkEquals(template.ids._2, that.ids._2)
      encoder.mkImplies(
        encoder.mkAnd(template.pathVar._2, that.pathVar._2),
        if (template.structure.lambda == that.structure.lambda) {
          val pairs = template.structure.dependencies zip that.structure.dependencies
          val filtered = pairs.filter(p => p._1 != p._2)
          if (filtered.isEmpty) {
            equals
          } else {
            val eqs = filtered.map(p => encoder.mkEquals(p._1, p._2))
            encoder.mkEquals(encoder.mkAnd(eqs : _*), equals)
          }
        } else {
          encoder.mkNot(equals)
        })
    }.toSeq
  }
}

