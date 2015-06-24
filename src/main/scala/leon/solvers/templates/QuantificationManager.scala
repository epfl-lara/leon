package leon
package solvers
package templates

import purescala.Common._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import Instantiation._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

case class Matcher[T](caller: T, tpe: TypeTree, args: Seq[T]) {
  override def toString = "M(" + caller + " : " + tpe + ", " + args.mkString("(",",",")") + ")"
}

case class IllegalQuantificationException(expr: Expr, msg: String)
  extends Exception(msg +" @ " + expr)

class QuantificationTemplate[T](
  val quantificationManager: QuantificationManager[T],
  val start: T,
  val qs: (Identifier, T),
  val holdVar: T,
  val guardVar: T,
  val quantifiers: Seq[(Identifier, T)],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Map[T, LambdaTemplate[T]]) {

  def instantiate(substMap: Map[T, T]): Instantiation[T] = {
    quantificationManager.instantiateQuantification(this, substMap)
  }
}

object QuantificationTemplate {
  def apply[T](
    encoder: TemplateEncoder[T],
    quantificationManager: QuantificationManager[T],
    pathVar: (Identifier, T),
    qs: (Identifier, T),
    holder: Identifier,
    guard: Identifier,
    quantifiers: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
    subst: Map[Identifier, T]
  ): QuantificationTemplate[T] = {

    val holders: (Identifier, T) = holder -> encoder.encodeId(holder)
    val guards: (Identifier, T) = guard -> encoder.encodeId(guard)

    val (clauses, blockers, applications, matchers, _) =
      Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas,
        substMap = subst + holders + guards + qs)

    new QuantificationTemplate[T](quantificationManager,
      pathVar._2, qs, holders._2, guards._2, quantifiers,
      condVars, exprVars, clauses, blockers, applications, matchers, lambdas)
  }
}

class QuantificationManager[T](encoder: TemplateEncoder[T]) extends LambdaManager[T](encoder) {

  private val nextHolder: () => T = {
    val id: Identifier = FreshIdentifier("ph", BooleanType)
    () => encoder.encodeId(id)
  }

  private val nextQ: () => T = {
    val id: Identifier = FreshIdentifier("q", BooleanType)
    () => encoder.encodeId(id)
  }

  private var quantificationsStack: List[Seq[Quantification]] = List(Seq.empty)
  private def quantifications: Seq[Quantification] = quantificationsStack.head
  private def quantifications_=(qs: Seq[Quantification]): Unit = {
    quantificationsStack = qs :: quantificationsStack.tail
  }

  private var instantiatedStack: List[Set[(T, Matcher[T])]] = List(Set.empty)
  private def instantiated: Set[(T, Matcher[T])] = instantiatedStack.head
  private def instantiated_=(ias: Set[(T, Matcher[T])]): Unit = {
    instantiatedStack = ias :: instantiatedStack.tail
  }

  private var knownStack: List[Set[T]] = List(Set.empty)
  private def known(idT: T): Boolean = knownStack.head(idT) || byID.isDefinedAt(idT)

  override def push(): Unit = {
    quantificationsStack = quantifications :: quantificationsStack
    instantiatedStack = instantiated :: instantiatedStack
    knownStack = knownStack.head :: knownStack
  }

  override def pop(lvl: Int): Unit = {
    quantificationsStack = quantificationsStack.drop(lvl)
    instantiatedStack = instantiatedStack.drop(lvl)
    knownStack = knownStack.drop(lvl)
  }

  def blockers: Seq[T] = quantifications.map(_.holdVar)

  override def registerFree(ids: Seq[(TypeTree, T)]): Unit = {
    super.registerFree(ids)
    knownStack = (knownStack.head ++ ids.map(_._2)) :: knownStack.tail
  }

  private class Quantification (
    val qVar: T,
    val holdVar: T,
    val guardVar: T,
    var currentHolder: T,
    val quantified: Set[T],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val matchers: Set[Matcher[T]],
    val lambdas: Map[T, LambdaTemplate[T]]) {

    def this(
      qVar: T, holdVar: T, guardVar: T, quantified: Set[T],
      condVars: Map[Identifier, T], exprVars: Map[Identifier, T],
      clauses: Seq[T], blockers: Map[T, Set[TemplateCallInfo[T]]], applications: Map[T, Set[App[T]]],
      matchers: Set[Matcher[T]], lambdas: Map[T, LambdaTemplate[T]]) = {
        this(qVar, holdVar, guardVar, nextHolder(), quantified,
          condVars, exprVars, clauses, blockers, applications, matchers, lambdas)
    }

    def substitute(subst: Map[T, T]) = {
      val substituter = encoder.substitute(subst)

      new Quantification (
        qVar, holdVar, guardVar, currentHolder,
        quantified, condVars, exprVars,
        clauses map substituter,
        blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        matchers map (m => m.copy(caller = substituter(m.caller), args = m.args.map(substituter))),
        lambdas map { case (idT, template) => substituter(idT) -> template.substitute(subst) }
      )
    }

    def instantiate(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
      val Matcher(caller, tpe, args) = matcher

      // Build a mapping from applications in the quantified statement to all potential concrete
      // applications previously encountered. Also make sure the current `app` is in the mapping
      // as other instantiations have been performed previously when the associated applications
      // were first encountered.
      val matcherMappings: Set[Set[(T, Matcher[T], Matcher[T])]] = matchers
        // 1. select an application in the quantified proposition for which the current app can
        //    be bound when generating the new constraints
        .filter(_.tpe == tpe)
        // 2. build the instantiation mapping associated to the chosen current application binding
        .flatMap { bindingMatcher => matchers
          // 2.1. select all potential matches for each quantified application
          .map { case qm @ Matcher(qcaller, qtpe, qargs) =>
            if (qm == bindingMatcher) {
              bindingMatcher -> Set(blocker -> matcher)
            } else {
              val instances: Set[(T, Matcher[T])] = instantiated.filter {
                case (b, m @ Matcher(caller, tpe, _)) => tpe == qtpe
              }

              // concrete applications can appear multiple times in the constraint, and this is also the case
              // for the current application for which we are generating the constraints
              val withCurrent = if (tpe == qtpe) instances + (blocker -> matcher) else instances

              qm -> withCurrent
            }
          }
          // 2.2. based on the possible bindings for each quantified application, build a set of
          //      instantiation mappings that can be used to instantiate all necessary constraints
          .foldLeft[Set[Set[(T, Matcher[T], Matcher[T])]]] (Set(Set.empty)) {
            case (mappings, (qm, instances)) => Set(instances.toSeq.flatMap {
              case (b, m) => mappings.map(mapping => mapping + ((b, qm, m)))
            } : _*)
          }
        }

      var instantiation = Instantiation.empty[T]

      for (mapping <- matcherMappings) {
        var constraints: List[T] = Nil
        var subst: Map[T, T] = Map.empty

        for {
          (b, Matcher(qcaller, _, qargs), Matcher(caller, _, args)) <- mapping
          _ = constraints :+= b
          _ = if (qcaller != caller) constraints :+= encoder.mkEquals(qcaller, caller)
          (qarg, arg) <- (qargs zip args)
        } if (subst.isDefinedAt(qarg)) {
          constraints :+= encoder.mkEquals(subst(qarg), arg)
        } else if (!quantified(qarg)) {
          constraints :+= encoder.mkEquals(qarg, arg)
        } else {
          subst += qarg -> arg
        }

        val enabler = if (constraints.size == 1) constraints.head else encoder.mkAnd(constraints : _*)
        val newHolder = nextHolder()

        val baseSubstMap = (condVars ++ exprVars).map { case (id, idT) => idT -> encoder.encodeId(id) }
        val lambdaSubstMap = lambdas map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
        val substMap = subst ++ baseSubstMap ++ lambdaSubstMap +
          (qVar -> currentHolder) + (guardVar -> enabler) + (holdVar -> newHolder)

        instantiation ++= Template.instantiate(encoder, QuantificationManager.this,
          clauses, blockers, applications, Seq.empty, Map.empty, lambdas, substMap)
        currentHolder = newHolder
      }

      instantiation
    }
  }

  def instantiateQuantification(template: QuantificationTemplate[T], substMap: Map[T, T]): Instantiation[T] = {

    val trueT = encoder.encodeExpr(Map.empty)(BooleanLiteral(true))
    val instantiationSubst: Map[T, T] = substMap + (template.guardVar -> trueT)

    val substituter = encoder.substitute(instantiationSubst)
    val matchers = template.matchers.map { case (b, ms) =>
      substituter(b) -> ms.map(m => m.copy(caller = substituter(m.caller), args = m.args.map(substituter)))
    }

    var instantiation: Instantiation[T] = Template.instantiate(encoder, this,
      template.clauses, template.blockers, template.applications,
      Seq.empty, Map.empty, template.lambdas, instantiationSubst)

    val quantified = template.quantifiers.map(_._2).toSet

    val allMatchers: Set[Matcher[T]] = {
      def rec(templates: Map[T, LambdaTemplate[T]]): Set[Matcher[T]] = templates.flatMap {
        case (_, template) => template.matchers.flatMap(_._2).toSet ++ rec(template.lambdas)
      }.toSet

      val allMatchers = template.matchers.flatMap(_._2).toSet ++ rec(template.lambdas)
      for (m @ Matcher(caller, tpe, args) <- allMatchers if args exists quantified) yield m
    }

    val matchQuorums: Seq[Set[Matcher[T]]] = allMatchers.subsets.filter { ms =>
      var doubled: Boolean = false
      var qs: Set[T] = Set.empty
      for (m @ Matcher(_, _, args) <- ms) {
        val qargs = (args filter quantified).toSet
        if ((qs & qargs).nonEmpty) doubled = true
        qs ++= qargs
      }

      !doubled && (qs == quantified)
    }.toSeq

    val newQuantifications = for (matchers <- matchQuorums) yield {
      val newQ = nextQ()

      new Quantification(newQ,
        template.holdVar, template.guardVar,
        newQ, // set template `qVar` as `currentHolder` to ensure blocking before first unfolding
        quantified,
        template.condVars,
        template.exprVars,
        template.clauses,
        template.blockers,
        template.applications,
        matchers,
        template.lambdas
      ).substitute(substMap)
    }

    val eqClause = {
      val qs = newQuantifications.map(_.qVar)
      val newQs = if (qs.isEmpty) trueT else if (qs.size == 1) qs.head else encoder.mkAnd(qs : _*)
      encoder.mkImplies(substMap(template.start), encoder.mkEquals(template.holdVar, newQs))
    }

    instantiation = (instantiation._1 :+ eqClause, instantiation._2, instantiation._3)

    val saved = instantiated

    for ((b, ms) <- matchers; bp = substituter(b); m <- ms) {
      val newM = m.copy(caller = substituter(m.caller), args = m.args.map(substituter))
      instantiation ++= instantiateMatcher(bp, newM)
    }

    for ((b, m) <- saved; q <- newQuantifications) {
      instantiation ++= q.instantiate(b, m)
    }

    quantifications ++= newQuantifications

    instantiation
  }

  def instantiateMatcher(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
    val qInst = if (instantiated(blocker -> matcher)) Instantiation.empty[T] else {
      var instantiation = Instantiation.empty[T]
      for (q <- quantifications) {
        instantiation ++= q.instantiate(blocker, matcher)
      }

      instantiated += (blocker -> matcher)

      instantiation
    }

    qInst
  }

}
