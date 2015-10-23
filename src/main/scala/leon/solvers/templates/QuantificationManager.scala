/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package templates

import leon.utils._
import purescala.Common._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import Instantiation._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

object Matcher {
  def argValue[T](arg: Either[T, Matcher[T]]): T = arg match {
    case Left(value) => value
    case Right(matcher) => matcher.encoded
  }
}

case class Matcher[T](caller: T, tpe: TypeTree, args: Seq[Either[T, Matcher[T]]], encoded: T) {
  override def toString = "M(" + caller + " : " + tpe + ", " + args.map(Matcher.argValue).mkString("(",",",")") + ")"

  def substitute(substituter: T => T): Matcher[T] = copy(
    caller = substituter(caller),
    args = args.map { arg => arg.left.map(substituter).right.map(_.substitute(substituter)) },
    encoded = substituter(encoded)
  )
}

case class IllegalQuantificationException(expr: Expr, msg: String)
  extends Exception(msg +" @ " + expr)

class QuantificationTemplate[T](
  val quantificationManager: QuantificationManager[T],
  val start: T,
  val qs: (Identifier, T),
  val q2s: (Identifier, T),
  val insts: (Identifier, T),
  val guardVar: T,
  val quantifiers: Seq[(Identifier, T)],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Seq[LambdaTemplate[T]]) {

  def substitute(substituter: T => T): QuantificationTemplate[T] = {
    new QuantificationTemplate[T](
      quantificationManager,
      substituter(start),
      qs,
      q2s,
      insts,
      guardVar,
      quantifiers,
      condVars,
      exprVars,
      clauses.map(substituter),
      blockers.map { case (b, fis) =>
        substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
      },
      applications.map { case (b, apps) =>
        substituter(b) -> apps.map(app => app.copy(caller = substituter(app.caller), args = app.args.map(substituter)))
      },
      matchers.map { case (b, ms) =>
        substituter(b) -> ms.map(_.substitute(substituter))
      },
      lambdas.map(_.substitute(substituter))
    )
  }
}

object QuantificationTemplate {
  def apply[T](
    encoder: TemplateEncoder[T],
    quantificationManager: QuantificationManager[T],
    pathVar: (Identifier, T),
    qs: (Identifier, T),
    q2: Identifier,
    inst: Identifier,
    guard: Identifier,
    quantifiers: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Seq[LambdaTemplate[T]],
    subst: Map[Identifier, T]
  ): QuantificationTemplate[T] = {

    val q2s: (Identifier, T) = q2 -> encoder.encodeId(q2)
    val insts: (Identifier, T) = inst -> encoder.encodeId(inst)
    val guards: (Identifier, T) = guard -> encoder.encodeId(guard)

    val (clauses, blockers, applications, matchers, _) =
      Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas,
        substMap = subst + q2s + insts + guards + qs)

    new QuantificationTemplate[T](quantificationManager,
      pathVar._2, qs, q2s, insts, guards._2, quantifiers,
      condVars, exprVars, clauses, blockers, applications, matchers, lambdas)
  }
}

class QuantificationManager[T](encoder: TemplateEncoder[T]) extends LambdaManager[T](encoder) {
  private val quantifications = new IncrementalSeq[MatcherQuantification]
  private val instantiated    = new InstantiationContext
  private val fInstantiated   = new InstantiationContext {
    override def apply(p: (T, Matcher[T])): Boolean =
      corresponding(p._2).exists(_._2.args == p._2.args)
  }

  private val known           = new IncrementalSet[T]

  private def correspond(qm: Matcher[T], m: Matcher[T]): Boolean = correspond(qm, m.caller, m.tpe)
  private def correspond(qm: Matcher[T], caller: T, tpe: TypeTree): Boolean = qm.tpe match {
    case _: FunctionType => qm.tpe == tpe && (qm.caller == caller || !known(caller))
    case _ => qm.tpe == tpe
  }

  private val uniformQuantMap: MutableMap[TypeTree, Seq[T]] = MutableMap.empty
  private val uniformQuantSet: MutableSet[T]                = MutableSet.empty

  def isQuantifier(idT: T): Boolean = uniformQuantSet(idT)
  private def uniformSubst(qs: Seq[(Identifier, T)]): Map[T, T] = {
    qs.groupBy(_._1.getType).flatMap { case (tpe, qst) =>
      val prev = uniformQuantMap.get(tpe) match {
        case Some(seq) => seq
        case None => Seq.empty
      }

      if (prev.size >= qst.size) {
        qst.map(_._2) zip prev.take(qst.size)
      } else {
        val (handled, newQs) = qst.splitAt(prev.size)
        val uQs = newQs.map(p => p._2 -> encoder.encodeId(p._1))

        uniformQuantMap(tpe) = prev ++ uQs.map(_._2)
        uniformQuantSet ++= uQs.map(_._2)

        (handled.map(_._2) zip prev) ++ uQs
      }
    }.toMap
  }

  override protected def incrementals: List[IncrementalState] =
    List(quantifications, instantiated, fInstantiated, known) ++ super.incrementals

  def assumptions: Seq[T] = quantifications.collect { case q: Quantification => q.currentQ2Var }.toSeq

  def instantiations: Seq[(T, Matcher[T])] = (instantiated.all ++ fInstantiated.all).toSeq

  def instantiations(caller: T, tpe: TypeTree): Seq[(T, Matcher[T])] =
    (instantiated.corresponding(caller, tpe) ++ fInstantiated.corresponding(caller, tpe)).toSeq

  override def registerFree(ids: Seq[(Identifier, T)]): Unit = {
    super.registerFree(ids)
    known ++= ids.map(_._2)
  }

  private type Context = Set[(T, Matcher[T])]

  private class ContextMap(
    private val tpeMap: MutableMap[TypeTree, Context] = MutableMap.empty,
    private val funMap: MutableMap[T, Context]        = MutableMap.empty
  ) {
    def +=(p: (T, Matcher[T])): Unit = {
      tpeMap(p._2.tpe) = tpeMap.getOrElse(p._2.tpe, Set.empty) + p
      p match {
        case (_, Matcher(caller, tpe: FunctionType, _, _)) if known(caller) =>
          funMap(caller) = funMap.getOrElse(caller, Set.empty) + p
        case _ =>
      }
    }

    def merge(that: ContextMap): this.type = {
      for ((tpe, values) <- that.tpeMap) tpeMap(tpe) = tpeMap.getOrElse(tpe, Set.empty) ++ values
      for ((caller, values) <- that.funMap) funMap(caller) = funMap.getOrElse(caller, Set.empty) ++ values
      this
    }

    @inline
    def get(m: Matcher[T]): Context = get(m.caller, m.tpe)

    def get(caller: T, tpe: TypeTree): Context =
      funMap.getOrElse(caller, Set.empty) ++ tpeMap.getOrElse(tpe, Set.empty)

    override def clone = new ContextMap(tpeMap.clone, funMap.clone)
  }

  private class InstantiationContext private (
    private var _instantiated : Context,
    private var _next         : Context,
    private var _map          : ContextMap,
    private var _count        : Int
  ) extends IncrementalState {

    def this() = this(Set.empty, Set.empty, new ContextMap, 0)
    def this(ctx: InstantiationContext) = this(ctx._instantiated, Set.empty, ctx._map.clone, ctx._count)

    private val stack = new scala.collection.mutable.Stack[(Context, Context, ContextMap, Int)]

    def clear(): Unit = {
      stack.clear()
      _instantiated = Set.empty
      _next = Set.empty
      _map = new ContextMap
      _count = 0
    }

    def reset(): Unit = clear()

    def push(): Unit = stack.push((_instantiated, _next, _map.clone, _count))

    def pop(): Unit = {
      val (instantiated, next, map, count) = stack.pop()
      _instantiated = instantiated
      _next = next
      _map = map
      _count = count
    }

    def count = _count
    def instantiated = _instantiated
    def all = _instantiated ++ _next

    def corresponding(m: Matcher[T]): Context = _map.get(m)
    def corresponding(caller: T, tpe: TypeTree): Context = _map.get(caller, tpe)

    def apply(p: (T, Matcher[T])): Boolean = _instantiated(p)

    def inc(): Unit = _count += 1

    def +=(p: (T, Matcher[T])): Unit = {
      if (!this(p)) _next += p
    }

    def ++=(ps: Iterable[(T, Matcher[T])]): Unit = {
      for (p <- ps) this += p
    }

    def consume: Iterator[(T, Matcher[T])] = {
      var n = _next
      _next = Set.empty

      new Iterator[(T, Matcher[T])] {
        def hasNext = n.nonEmpty
        def next = {
          val p @ (b,m) = n.head
          _instantiated += p
          _map += p
          n -= p
          p
        }
      }
    }

    def instantiateNext: Instantiation[T] = {
      var instantiation = Instantiation.empty[T]
      for ((b,m) <- consume) {
        println("consuming " + (b -> m))
        for (q <- quantifications) {
          instantiation ++= q.instantiate(b, m)(this)
        }
      }
      instantiation
    }

    def merge(that: InstantiationContext): this.type = {
      _instantiated ++= that._instantiated
      _next ++= that._next
      _map.merge(that._map)
      _count = _count max that._count
      this
    }
  }

  private trait MatcherQuantification {
    val quantified: Set[T]
    val matchers: Set[Matcher[T]]
    val allMatchers: Map[T, Set[Matcher[T]]]
    val condVars: Map[Identifier, T]
    val exprVars: Map[Identifier, T]
    val clauses: Seq[T]
    val blockers: Map[T, Set[TemplateCallInfo[T]]]
    val applications: Map[T, Set[App[T]]]
    val lambdas: Seq[LambdaTemplate[T]]

    private def mappings(blocker: T, matcher: Matcher[T], instCtx: InstantiationContext): Set[(T, Map[T, T])] = {

      // Build a mapping from applications in the quantified statement to all potential concrete
      // applications previously encountered. Also make sure the current `app` is in the mapping
      // as other instantiations have been performed previously when the associated applications
      // were first encountered.
      val matcherMappings: Set[Set[(T, Matcher[T], Matcher[T])]] = matchers
        // 1. select an application in the quantified proposition for which the current app can
        //    be bound when generating the new constraints
        .filter(qm => correspond(qm, matcher))
        // 2. build the instantiation mapping associated to the chosen current application binding
        .flatMap { bindingMatcher =>

          // 2.1. select all potential matches for each quantified application
          val matcherToInstances = matchers
            .map(qm => if (qm == bindingMatcher) {
              bindingMatcher -> Set(blocker -> matcher)
            } else {
              qm -> instCtx.corresponding(qm)
            }).toMap

          // 2.2. based on the possible bindings for each quantified application, build a set of
          //      instantiation mappings that can be used to instantiate all necessary constraints
          extractMappings(matcherToInstances)
        }

      for (mapping <- matcherMappings) yield extractSubst(quantified, mapping)
    }

    def instantiate(blocker: T, matcher: Matcher[T])(implicit instCtx: InstantiationContext): Instantiation[T] = {
      var instantiation = Instantiation.empty[T]

      for ((enabler, subst) <- mappings(blocker, matcher, instCtx)) {
        val baseSubstMap = (condVars ++ exprVars).map { case (id, idT) => idT -> encoder.encodeId(id) }
        val lambdaSubstMap = lambdas map(lambda => lambda.ids._2 -> encoder.encodeId(lambda.ids._1))
        val substMap = subst ++ baseSubstMap ++ lambdaSubstMap ++ instanceSubst(enabler)

        instantiation ++= Template.instantiate(encoder, QuantificationManager.this,
          clauses, blockers, applications, Seq.empty, Map.empty[T, Set[Matcher[T]]], lambdas, substMap)

        val substituter = encoder.substitute(substMap)
        for ((b, ms) <- allMatchers; m <- ms if !matchers(m)) {
          println(m.substitute(substituter))
          instCtx += substituter(b) -> m.substitute(substituter)
        }
      }

      instantiation
    }

    protected def instanceSubst(enabler: T): Map[T, T]
  }

  private class Quantification (
    val qs: (Identifier, T),
    val q2s: (Identifier, T),
    val insts: (Identifier, T),
    val guardVar: T,
    val quantified: Set[T],
    val matchers: Set[Matcher[T]],
    val allMatchers: Map[T, Set[Matcher[T]]],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Seq[LambdaTemplate[T]]) extends MatcherQuantification {

    var currentQ2Var: T = qs._2

    protected def instanceSubst(enabler: T): Map[T, T] = {
      val nextQ2Var = encoder.encodeId(q2s._1)

      val subst = Map(qs._2 -> currentQ2Var, guardVar -> enabler,
        q2s._2 -> nextQ2Var, insts._2 -> encoder.encodeId(insts._1))

      currentQ2Var = nextQ2Var
      subst
    }
  }

  private val blockerId = FreshIdentifier("blocker", BooleanType, true)
  private val blockerCache: MutableMap[T, T] = MutableMap.empty

  private class Axiom (
    val start: T,
    val blocker: T,
    val guardVar: T,
    val quantified: Set[T],
    val matchers: Set[Matcher[T]],
    val allMatchers: Map[T, Set[Matcher[T]]],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Seq[LambdaTemplate[T]]) extends MatcherQuantification {

    protected def instanceSubst(enabler: T): Map[T, T] = {
      val newBlocker = blockerCache.get(enabler) match {
        case Some(b) => b
        case None =>
          val nb = encoder.encodeId(blockerId)
          blockerCache(enabler) = nb
          blockerCache(nb) = nb
          nb
      }

      Map(guardVar -> encoder.mkAnd(start, enabler), blocker -> newBlocker)
    }
  }

  private def extractMappings(
    bindings: Map[Matcher[T], Set[(T, Matcher[T])]]
  ): Set[Set[(T, Matcher[T], Matcher[T])]] = {
    val allMappings = bindings.foldLeft[Set[Set[(T, Matcher[T], Matcher[T])]]](Set(Set.empty)) {
      case (mappings, (qm, instances)) => Set(instances.toSeq.flatMap {
        case (b, m) => mappings.map(mapping => mapping + ((b, qm, m)))
      } : _*)
    }

    def subBindings(b: T, sm: Matcher[T], m: Matcher[T]): Set[(T, Matcher[T], Matcher[T])] = {
      (for ((sarg, arg) <- sm.args zip m.args) yield {
        (sarg, arg) match {
          case (Right(sargm), Right(argm)) => Set((b, sargm, argm)) ++ subBindings(b, sargm, argm)
          case _ => Set.empty[(T, Matcher[T], Matcher[T])]
        }
      }).flatten.toSet
    }

    allMappings.filter { s =>
      val withSubs = s ++ s.flatMap { case (b, sm, m) => subBindings(b, sm, m) }
      withSubs.groupBy(_._2).forall(_._2.size == 1)
    }

    allMappings
  }

  private def extractSubst(quantified: Set[T], mapping: Set[(T, Matcher[T], Matcher[T])]): (T, Map[T,T]) = {
    var constraints: List[T] = Nil
    var subst: Map[T, T] = Map.empty

    for {
      (b, Matcher(qcaller, _, qargs, _), Matcher(caller, _, args, _)) <- mapping
      _ = constraints :+= b
      (qarg, arg) <- (qargs zip args)
      argVal = Matcher.argValue(arg)
    } qarg match {
      case Left(quant) if subst.isDefinedAt(quant) =>
        constraints :+= encoder.mkEquals(quant, argVal)
      case Left(quant) if quantified(quant) =>
        subst += quant -> argVal
      case _ =>
        constraints :+= encoder.mkEquals(Matcher.argValue(qarg), argVal)
    }

    val enabler =
      if (constraints.isEmpty) trueT
      else if (constraints.size == 1) constraints.head
      else encoder.mkAnd(constraints : _*)

    (encoder.substitute(subst)(enabler), subst)
  }

  private def extractQuorums(
    quantified: Set[T],
    matchers: Set[Matcher[T]],
    lambdas: Seq[LambdaTemplate[T]]
  ): Seq[Set[Matcher[T]]] = {
    val extMatchers: Set[Matcher[T]] = {
      def rec(templates: Seq[LambdaTemplate[T]]): Set[Matcher[T]] =
        templates.foldLeft(Set.empty[Matcher[T]]) {
          case (matchers, template) => matchers ++ template.matchers.flatMap(_._2) ++ rec(template.lambdas)
        }

      matchers ++ rec(lambdas)
    }

    val quantifiedMatchers = for {
      m @ Matcher(_, _, args, _) <- extMatchers
      if args exists (_.left.exists(quantified))
    } yield m

    purescala.Quantification.extractQuorums(quantifiedMatchers, quantified,
      (m: Matcher[T]) => m.args.collect { case Right(m) if quantifiedMatchers(m) => m }.toSet,
      (m: Matcher[T]) => m.args.collect { case Left(a) if quantified(a) => a }.toSet)
  }

  private val lambdaAxioms: MutableSet[(LambdaTemplate[T], Seq[(Identifier, T)])] = MutableSet.empty

  def instantiateAxiom(template: LambdaTemplate[T], substMap: Map[T, T]): Instantiation[T] = {
    val quantifiers = template.arguments map {
      case (id, idT) => id -> substMap(idT)
    } filter (p => isQuantifier(p._2))

    if (quantifiers.isEmpty || lambdaAxioms(template -> quantifiers)) {
      Instantiation.empty[T]
    } else {
      lambdaAxioms += template -> quantifiers
      val blockerT = encoder.encodeId(blockerId)

      val guard = FreshIdentifier("guard", BooleanType, true)
      val guardT = encoder.encodeId(guard)

      val substituter = encoder.substitute(substMap + (template.start -> blockerT))
      val allMatchers = template.matchers map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter)) }
      val qMatchers = allMatchers.flatMap(_._2).toSet

      val encArgs = template.args map substituter
      val app = Application(Variable(template.ids._1), template.arguments.map(_._1.toVariable))
      val appT = encoder.encodeExpr((template.arguments.map(_._1) zip encArgs).toMap + template.ids)(app)
      val selfMatcher = Matcher(template.ids._2, template.tpe, encArgs.map(Left(_)), appT)

      val enablingClause = encoder.mkImplies(guardT, blockerT)

      instantiateAxiom(
        substMap(template.start),
        blockerT,
        guardT,
        quantifiers,
        qMatchers,
        allMatchers + (template.start -> (allMatchers.getOrElse(template.start, Set.empty) + selfMatcher)),
        template.condVars map { case (id, idT) => id -> substituter(idT) },
        template.exprVars map { case (id, idT) => id -> substituter(idT) },
        (template.clauses map substituter) :+ enablingClause,
        template.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        template.applications map { case (b, apps) =>
          substituter(b) -> apps.map(app => app.copy(caller = substituter(app.caller), args = app.args.map(substituter)))
        },
        template.lambdas map (_.substitute(substituter))
      )
    }
  }

  def instantiateAxiom(
    start: T,
    blocker: T,
    guardVar: T,
    quantifiers: Seq[(Identifier, T)],
    matchers: Set[Matcher[T]],
    allMatchers: Map[T, Set[Matcher[T]]],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    clauses: Seq[T],
    blockers: Map[T, Set[TemplateCallInfo[T]]],
    applications: Map[T, Set[App[T]]],
    lambdas: Seq[LambdaTemplate[T]]
  ): Instantiation[T] = {
    val quantified = quantifiers.map(_._2).toSet
    val matchQuorums = extractQuorums(quantified, matchers, lambdas)

    var instantiation = Instantiation.empty[T]

    for (matchers <- matchQuorums) {
      val axiom = new Axiom(start, blocker, guardVar, quantified,
        matchers, allMatchers, condVars, exprVars,
        clauses, blockers, applications, lambdas
      )

      quantifications += axiom

      for (instCtx <- List(instantiated, fInstantiated)) {
        val pCtx = new InstantiationContext(instCtx)

        for ((b, m) <- pCtx.instantiated) {
          instantiation ++= axiom.instantiate(b, m)(pCtx)
        }

        for (i <- (1 to instCtx.count)) {
          instantiation ++= pCtx.instantiateNext
        }

        instCtx.merge(pCtx)
      }
    }

    val quantifierSubst = uniformSubst(quantifiers)
    val substituter = encoder.substitute(quantifierSubst)

    for (m <- matchers) {
      instantiation ++= instantiateMatcher(trueT, m.substitute(substituter), fInstantiated)
    }

    instantiation
  }

  def instantiateQuantification(template: QuantificationTemplate[T], substMap: Map[T, T]): Instantiation[T] = {
    val quantified = template.quantifiers.map(_._2).toSet
    val matchQuorums = extractQuorums(quantified, template.matchers.flatMap(_._2).toSet, template.lambdas)

    var instantiation = Instantiation.empty[T]

    val qs = for (matchers <- matchQuorums) yield {
      val newQ = encoder.encodeId(template.qs._1)
      val subst = substMap + (template.qs._2 -> newQ)

      val substituter = encoder.substitute(subst)
      val quantification = new Quantification(template.qs._1 -> newQ,
        template.q2s, template.insts, template.guardVar,
        quantified,
        matchers map (_.substitute(substituter)),
        template.matchers map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter)) },
        template.condVars,
        template.exprVars,
        template.clauses map substituter,
        template.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        template.applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        template.lambdas map (_.substitute(substituter))
      )

      quantifications += quantification

      for (instCtx <- List(instantiated, fInstantiated)) {
        val pCtx = new InstantiationContext(instCtx)

        for ((b, m) <- pCtx.instantiated) {
          instantiation ++= quantification.instantiate(b, m)(pCtx)
        }

        for (i <- (1 to instCtx.count)) {
          instantiation ++= pCtx.instantiateNext
        }

        instCtx.merge(pCtx)
      }

      quantification.qs._2
    }

    instantiation = instantiation withClause {
      val newQs =
        if (qs.isEmpty) trueT
        else if (qs.size == 1) qs.head
        else encoder.mkAnd(qs : _*)
      encoder.mkImplies(substMap(template.start), encoder.mkEquals(substMap(template.qs._2), newQs))
    }

    val quantifierSubst = uniformSubst(template.quantifiers)
    val substituter = encoder.substitute(substMap ++ quantifierSubst)

    for ((_, ms) <- template.matchers; m <- ms) {
      instantiation ++= instantiateMatcher(trueT, m.substitute(substituter), fInstantiated)
    }

    instantiation
  }

  private def instantiateMatcher(blocker: T, matcher: Matcher[T], instCtx: InstantiationContext): Instantiation[T] = {
    if (instCtx(blocker -> matcher)) {
      Instantiation.empty[T]
    } else {
      println("instantiating " + (blocker -> matcher))
      var instantiation: Instantiation[T] = Instantiation.empty

      val pCtx = new InstantiationContext(instCtx)
      pCtx += blocker -> matcher
      pCtx.inc() // pCtx.count == instCtx.count + 1

      // we just inc()'ed so we can start at 1 (instCtx.count is guaranteed to have increased)
      for (i <- (1 to instCtx.count)) {
        instantiation ++= pCtx.instantiateNext
      }

      instantiation ++= instCtx.merge(pCtx).instantiateNext

      instantiation
    }
  }

  def instantiateMatcher(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
    instantiateMatcher(blocker, matcher, instantiated)
  }
}
