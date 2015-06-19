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

  private val stdQuantifiers: MutableMap[TypeTree, Seq[T]] = MutableMap.empty
  private val quantified: MutableSet[T] = MutableSet.empty

  private def standardQuantifiers(tpe: TypeTree, count: Int): Seq[T] = {
    val quantifiers = stdQuantifiers.getOrElse(tpe, Seq.empty)
    val currentCount = quantifiers.size

    if (currentCount >= count) quantifiers.take(count) else {
      val newQuantifiers = List.range(0, count - currentCount).map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
      quantified ++= newQuantifiers

      val allQuantifiers = quantifiers ++ newQuantifiers
      stdQuantifiers(tpe) = allQuantifiers
      allQuantifiers
    }
  }

  private def freshQuantifierSubst: Map[T, T] = stdQuantifiers.flatMap { case (tpe, ids) =>
    ids zip List.range(0, ids.size).map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
  }.toMap

  private val nextHolder: () => T = {
    val id: Identifier = FreshIdentifier("ph", BooleanType)
    () => encoder.encodeId(id)
  }

  private val nextQ: () => T = {
    val id: Identifier = FreshIdentifier("q", BooleanType)
    () => encoder.encodeId(id)
  }

  private type Bindings = Set[(Option[T], TypeTree, Int, T)]
  private var bindingsStack: List[Bindings] = List(Set.empty)
  private def bindings: Bindings = bindingsStack.head
  private def bindings_=(bs: Bindings): Unit = {
    bindingsStack = bs :: bindingsStack.tail
  }

  private var quantificationsStack: List[Seq[Quantification]] = List(Seq.empty)
  private def quantifications: Seq[Quantification] = quantificationsStack.head
  private def quantifications_=(qs: Seq[Quantification]): Unit = {
    quantificationsStack = qs :: quantificationsStack.tail
  }

  private var instantiatedMatchersStack: List[Seq[(T, Matcher[T], Map[T,T])]] = List(Seq.empty)
  private def instantiatedMatchers: Seq[(T, Matcher[T], Map[T,T])] = instantiatedMatchersStack.head
  private def instantiatedMatchers_=(ias: Seq[(T, Matcher[T], Map[T,T])]): Unit = {
    instantiatedMatchersStack = ias :: instantiatedMatchersStack.tail
  }

  private var boundMatchersStack: List[Set[(T, Matcher[T])]] = List(Set.empty)
  private def boundMatchers: Set[(T, Matcher[T])] = boundMatchersStack.head
  private def boundMatchers_=(bas: Set[(T, Matcher[T])]): Unit = {
    boundMatchersStack = bas :: boundMatchersStack.tail
  }

  private var knownStack: List[Set[T]] = List(Set.empty)
  private def known(idT: T): Boolean = knownStack.head(idT) || byID.isDefinedAt(idT)

  override def push(): Unit = {
    bindingsStack = bindings :: bindingsStack
    quantificationsStack = quantifications :: quantificationsStack
    instantiatedMatchersStack = instantiatedMatchers :: instantiatedMatchersStack
    boundMatchersStack = boundMatchers :: boundMatchersStack
    knownStack = knownStack.head :: knownStack
  }

  override def pop(lvl: Int): Unit = {
    bindingsStack = bindingsStack.drop(lvl)
    quantificationsStack = quantificationsStack.drop(lvl)
    instantiatedMatchersStack = instantiatedMatchersStack.drop(lvl)
    boundMatchersStack = boundMatchersStack.drop(lvl)
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
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val matchers: Set[Matcher[T]],
    val lambdas: Map[T, LambdaTemplate[T]]) {

    def this(
      qVar: T, holdVar: T, guardVar: T,
      condVars: Map[Identifier, T], exprVars: Map[Identifier, T],
      clauses: Seq[T], blockers: Map[T, Set[TemplateCallInfo[T]]], applications: Map[T, Set[App[T]]],
      matchers: Set[Matcher[T]], lambdas: Map[T, LambdaTemplate[T]]) = {
        this(qVar, holdVar, guardVar, nextHolder(),
          condVars, exprVars, clauses, blockers, applications, matchers, lambdas)
    }

    def substitute(subst: Map[T, T]) = {
      val substituter = encoder.substitute(subst)

      new Quantification (
        qVar, holdVar, guardVar, currentHolder,
        condVars, exprVars,
        clauses map substituter,
        blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        matchers map { case m @ Matcher(caller, _, args) =>
          m.copy(caller = substituter(caller), args = args.map(substituter))
        },
        lambdas map { case (idT, template) => substituter(idT) -> template.substitute(subst) }
      )
    }

    def instantiate(blocker: T, matcher: Matcher[T], quantifierSubst: Map[T, T]): Instantiation[T] = {
      val Matcher(caller, tpe, args) = matcher

      // Build a mapping from applications in the quantified statement to all potential concrete
      // applications previously encountered. Also make sure the current `app` is in the mapping
      // as other instantiations have been performed previously when the associated applications
      // were first encountered.
      val matcherMappings: Set[Set[(T, Matcher[T], Matcher[T])]] = matchers
        // 1. select an application in the quantified proposition for which the current app can
        //    be bound when generating the new constraints
        .filter(qm => qm.caller == caller || (qm.tpe == tpe && !known(qm.caller)))
        // 2. build the instantiation mapping associated to the chosen current application binding
        .flatMap { bindingMatcher => matchers
          // 2.1. select all potential matches for each quantified application
          .map { case qm @ Matcher(qcaller, qtpe, qargs) =>
            if (qm == bindingMatcher) {
              bindingMatcher -> Set(blocker -> matcher)
            } else {
              val instances: Seq[(T, Matcher[T])] = instantiatedMatchers.collect {
                case (b, m @ Matcher(caller, tpe, _), _) if tpe == qtpe && (qcaller == caller || !known(caller)) => (b, m)
              }

              // concrete applications can appear multiple times in the constraint, and this is also the case
              // for the current application for which we are generating the constraints
              val withCurrent = if (tpe == qtpe && (qcaller == caller || !known(caller))) {
                instances :+ (blocker -> matcher)
              } else instances

              // add quantified application to instances for constraints that depend on free variables
              // this also make sure that constraints that don't depend on all variables will also be instantiated
              // Note: we can use `blocker` here as the blocker since it is guaranteed true in this branch
              val withAll = withCurrent :+ (blocker -> qm.copy(args = qm.args.map(a => quantifierSubst.getOrElse(a, a))))

              qm -> withAll
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
        } if (subst.isDefinedAt(qarg) || !quantified(qarg)) {
          constraints :+= encoder.mkEquals(qarg, arg)
        } else {
          subst += qarg -> arg
        }

        for ((q,nq) <- quantifierSubst if !subst.isDefinedAt(q)) {
          subst += q -> nq
        }

        val enabler = if (constraints.size == 1) constraints.head else encoder.mkAnd(constraints : _*)
        val newHolder = nextHolder()

        val lambdaSubstMap = lambdas map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
        val substMap = subst ++ lambdaSubstMap + (qVar -> currentHolder) + (guardVar -> enabler) + (holdVar -> newHolder)
        val substituter = encoder.substitute(substMap)

        val newClauses = clauses map substituter
        val newBlockers = blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        }

        instantiation ++= (newClauses, newBlockers, Map.empty)

        for ((idT, lambda) <- lambdas) {
          val newIdT = substituter(idT)
          val newTemplate = lambda.substitute(substMap)
          instantiation ++= instantiateLambda(newIdT, newTemplate)
        }

        for ((b, apps) <- applications; bp = substituter(b); app <- apps) {
          val newApp = app.copy(caller = substituter(app.caller), args = app.args.map(substituter))
          instantiation ++= instantiateApp(bp, newApp)
        }

        currentHolder = newHolder
      }

      instantiation
    }
  }

  def instantiateQuantification(template: QuantificationTemplate[T], substMap: Map[T, T]): Instantiation[T] = {

    val (quantification, matchers) = {
      val quantified = template.quantifiers.map(_._2).toSet

      val allMatchers: Set[Matcher[T]] = {
        def rec(templates: Map[T, LambdaTemplate[T]]): Set[Matcher[T]] = templates.flatMap {
          case (_, template) => template.matchers.flatMap(_._2).toSet ++ rec(template.lambdas)
        }.toSet

        val allMatchers = template.matchers.flatMap(_._2).toSet ++ rec(template.lambdas)
        for (m @ Matcher(caller, tpe, args) <- allMatchers if args exists quantified) yield m
      }

      val q = new Quantification(
        template.qs._2,
        template.holdVar,
        template.guardVar,
        template.qs._2, // this Quantification will never be instantiated, so this increases sanity
        template.condVars,
        template.exprVars,
        template.clauses,
        template.blockers,
        template.applications,
        allMatchers,
        template.lambdas
      )

      val tpeCounts = template.quantifiers.groupBy(_._1.getType).mapValues(_.map(_._2).toSeq)
      val qSubst = tpeCounts.flatMap { case (tpe, idTs) => idTs zip standardQuantifiers(tpe, idTs.size) }.toMap
      val subst = substMap ++ qSubst

      val quantification = q.substitute(subst)

      val substituter = encoder.substitute(subst)
      val matchers = template.matchers.map { case (b, ms) =>
        substituter(b) -> ms.map(m => m.copy(caller = substituter(m.caller), args = m.args.map(substituter)))
      }

      (quantification, matchers)
    }

    val quantifierSubst: Map[T,T] = freshQuantifierSubst

    var instantiation: Instantiation[T] = Template.instantiate(encoder, this,
      quantification.clauses, quantification.blockers, quantification.applications,
      Seq.empty, matchers, quantification.lambdas,
      quantifierSubst + (quantification.guardVar -> encoder.encodeExpr(Map.empty)(BooleanLiteral(true)))
    )

    val qBindings: Bindings = quantification.matchers.flatMap {
      case Matcher(caller, tpe, args) => args.zipWithIndex.collect {
        case (qid, idx) if quantified(qid) =>
          (if (known(caller)) Some(caller) else None, tpe, idx, qid)
      }
    }

    val (callerBindings, typeBindings) = (bindings ++ qBindings).partition(_._1.isDefined)

    val callerMap: Map[(T, Int), Set[T]] = callerBindings.groupBy(p => (p._1.get, p._3)).mapValues(_.map(_._4))
    val typeMap: Map[(TypeTree, Int), Set[T]] = typeBindings.groupBy(p => (p._2, p._3)).mapValues(_.map(_._4))

    val pairs: Set[(T, T)] = qBindings.flatMap { case (optIdT, tpe, idx, q) =>
      val matches = typeMap.getOrElse(tpe -> idx, Set.empty) ++ optIdT.toSeq.flatMap(idT => callerMap(idT -> idx))
      matches.map(q2 => q -> q2)
    }

    val mappings: List[Map[T, T]] =
      pairs.groupBy(_._1).toSeq.foldLeft(List(Map.empty[T, T])) {
        case (mappings, (_, pairs)) => pairs.toList.flatMap(p => mappings.map(mapping => mapping + p))
      }

    val newQuantifications = for (mapping <- mappings) yield {
      val newQ = encoder.encodeId(FreshIdentifier("q", BooleanType))

      val freshConds = quantification.condVars.map(p => p._1.freshen -> p._2)
      val freshExprs = quantification.exprVars.map(p => p._1.freshen -> p._2)

      val substMap: Map[T, T] = mapping ++
        (freshConds ++ freshExprs).map { case (id, idT) => idT -> encoder.encodeId(id) } ++
        quantification.lambdas.map { case (idT, template) => idT -> encoder.encodeId(template.id) } +
        (quantification.qVar -> newQ)

      val substituter = encoder.substitute(substMap)

      new Quantification(newQ,
        quantification.holdVar, quantification.guardVar,
        newQ, // set the fresh qVar as `currentHolder` to ensure blocking before first unfolding
        freshConds mapValues substituter,
        freshExprs mapValues substituter,
        quantification.clauses map substituter,
        quantification.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        quantification.applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        quantification.matchers map { case m @ Matcher(caller, _, args) =>
          m.copy(caller = substituter(caller), args = args.map(substituter))
        },
        quantification.lambdas map { case (idT, template) => substituter(idT) -> template.substitute(mapping) }
      )
    }

    val eqClause = {
      val qs = newQuantifications.map(_.qVar)
      val newQs = if (qs.size > 1) encoder.mkAnd(qs : _*) else qs.head
      encoder.mkImplies(substMap(template.start), encoder.mkEquals(template.holdVar, newQs))
    }

    instantiation = (instantiation._1 :+ eqClause, instantiation._2, instantiation._3)

    // ensure the `quantifierSubst` associated to each instantiated app covers all necessary
    // parameters for the current new quantifications
    instantiatedMatchers = for ((b, m, qSubst) <- instantiatedMatchers) yield {
      val nqSubst = if (qSubst.size == stdQuantifiers.map(_._2.size).sum) qSubst else {
        stdQuantifiers.flatMap { case (tpe, ids) =>
          val recent = ids.dropWhile(qSubst.isDefinedAt)
          recent zip recent.map(_ => encoder.encodeId(FreshIdentifier("x", tpe)))
        }.toMap
      }

      (b, m, nqSubst)
    }

    quantifications ++= newQuantifications

    for ((b, m, qSubst) <- instantiatedMatchers; q <- newQuantifications) {
      instantiation ++= q.instantiate(b, m, qSubst)
    }

    instantiation
  }

  def instantiateMatcher(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
    val qInst = if (boundMatchers(blocker -> matcher)) Instantiation.empty[T] else {
      val quantifierSubst: Map[T, T] = freshQuantifierSubst

      var instantiation = Instantiation.empty[T]
      for (q <- quantifications) {
        instantiation ++= q.instantiate(blocker, matcher, quantifierSubst)
      }

      instantiatedMatchers :+= (blocker, matcher, quantifierSubst)
      boundMatchers += (blocker -> matcher)

      instantiation
    }

    qInst
  }

}
