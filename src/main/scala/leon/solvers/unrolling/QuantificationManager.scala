/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package unrolling

import leon.utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps._
import purescala.Quantification.{QuantificationTypeMatcher => QTM, QuantificationMatcher => QM, Domains}

import evaluators._

import Instantiation._
import Template._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, Stack => MutableStack, Queue}

case class Matcher[T](caller: T, tpe: TypeTree, args: Seq[Arg[T]], encoded: T) {
  override def toString = caller + args.map {
    case Right(m) => m.toString
    case Left(v) => v.toString
  }.mkString("(",",",")")

  def substitute(substituter: T => T, matcherSubst: Map[T, Matcher[T]]): Matcher[T] = copy(
    caller = substituter(caller),
    args = args.map {
      case Left(v) => matcherSubst.get(v) match {
        case Some(m) => Right(m)
        case None => Left(substituter(v))
      }
      case Right(m) => Right(m.substitute(substituter, matcherSubst))
    },
    encoded = substituter(encoded)
  )
}

class QuantificationTemplate[T](
  val quantificationManager: QuantificationManager[T],
  val pathVar: (Identifier, T),
  val qs: (Identifier, T),
  val q2s: (Identifier, T),
  val insts: (Identifier, T),
  val guardVar: T,
  val quantifiers: Seq[(Identifier, T)],
  val condVars: Map[Identifier, T],
  val exprVars: Map[Identifier, T],
  val condTree: Map[Identifier, Set[Identifier]],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val applications: Map[T, Set[App[T]]],
  val matchers: Map[T, Set[Matcher[T]]],
  val lambdas: Seq[LambdaTemplate[T]],
  val structure: Forall,
  val dependencies: Map[Identifier, T],
  val forall: Forall,
  stringRepr: () => String) {

  lazy val start = pathVar._2
  lazy val key: (Forall, Seq[T]) = (structure, {
    var cls: Seq[T] = Seq.empty
    purescala.ExprOps.preTraversal {
      case Variable(id) => cls ++= dependencies.get(id)
      case _ =>
    } (structure)
    cls
  })

  def substitute(substituter: T => T, matcherSubst: Map[T, Matcher[T]]): QuantificationTemplate[T] = {
    new QuantificationTemplate[T](
      quantificationManager,
      pathVar._1 -> substituter(start),
      qs,
      q2s,
      insts,
      guardVar,
      quantifiers,
      condVars,
      exprVars,
      condTree,
      clauses.map(substituter),
      blockers.map { case (b, fis) =>
        substituter(b) -> fis.map(fi => fi.copy(
          args = fi.args.map(_.substitute(substituter, matcherSubst))
        ))
      },
      applications.map { case (b, apps) =>
        substituter(b) -> apps.map(app => app.copy(
          caller = substituter(app.caller),
          args = app.args.map(_.substitute(substituter, matcherSubst))
        ))
      },
      matchers.map { case (b, ms) =>
        substituter(b) -> ms.map(_.substitute(substituter, matcherSubst))
      },
      lambdas.map(_.substitute(substituter, matcherSubst)),
      structure,
      dependencies.map { case (id, value) => id -> substituter(value) },
      forall,
      stringRepr
    )
  }

  private lazy val str : String = stringRepr()
  override def toString : String = str
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
    condTree: Map[Identifier, Set[Identifier]],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Seq[LambdaTemplate[T]],
    baseSubstMap: Map[Identifier, T],
    dependencies: Map[Identifier, T],
    proposition: Forall
  ): QuantificationTemplate[T] = {

    val q2s: (Identifier, T) = q2 -> encoder.encodeId(q2)
    val insts: (Identifier, T) = inst -> encoder.encodeId(inst)
    val guards: (Identifier, T) = guard -> encoder.encodeId(guard)

    val (clauses, blockers, applications, functions, matchers, templateString) =
      Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas, Seq.empty,
        substMap = baseSubstMap + q2s + insts + guards + qs)

    val (structuralQuant, deps) = normalizeStructure(proposition)
    val keyDeps = deps.map { case (id, dep) => id -> encoder.encodeExpr(dependencies)(dep) }

    new QuantificationTemplate[T](quantificationManager,
      pathVar, qs, q2s, insts, guards._2, quantifiers, condVars, exprVars, condTree,
      clauses, blockers, applications, matchers, lambdas, structuralQuant, keyDeps, proposition,
      () => "Template for " + proposition + " is :\n" + templateString())
  }
}

class QuantificationManager[T](encoder: TemplateEncoder[T]) extends LambdaManager[T](encoder) {
  private[solvers] val quantifications = new IncrementalSeq[MatcherQuantification]

  private val instCtx         = new InstantiationContext

  private val ignoredMatchers = new IncrementalSeq[(Int, Set[T], Matcher[T])]
  private val ignoredSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Int, Set[T], Map[T,Arg[T]])]]
  private val handledSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Set[T], Map[T,Arg[T]])]]

  private val lambdaAxioms    = new IncrementalSet[(LambdaStructure[T], Seq[(Identifier, T)])]
  private val templates       = new IncrementalMap[(Expr, Seq[T]), T]

  override protected def incrementals: List[IncrementalState] =
    List(quantifications, instCtx, ignoredMatchers, ignoredSubsts,
      handledSubsts, lambdaAxioms, templates) ++ super.incrementals

  private var currentGen = 0

  private sealed abstract class MatcherKey(val tpe: TypeTree)
  private case class CallerKey(caller: T, tt: TypeTree) extends MatcherKey(tt)
  private case class LambdaKey(lambda: Lambda, tt: TypeTree) extends MatcherKey(tt)
  private case class TypeKey(tt: TypeTree) extends MatcherKey(tt)

  private def matcherKey(caller: T, tpe: TypeTree): MatcherKey = tpe match {
    case ft: FunctionType if knownFree(ft)(caller) => CallerKey(caller, tpe)
    case _: FunctionType if byID.isDefinedAt(caller) => LambdaKey(byID(caller).structure.lambda, tpe)
    case _ => TypeKey(tpe)
  }

  @inline
  private def correspond(qm: Matcher[T], m: Matcher[T]): Boolean =
    correspond(qm, m.caller, m.tpe)

  private def correspond(qm: Matcher[T], caller: T, tpe: TypeTree): Boolean = {
    val qkey = matcherKey(qm.caller, qm.tpe)
    val key = matcherKey(caller, tpe)
    qkey == key || (qkey.tpe == key.tpe && (qkey.isInstanceOf[TypeKey] || key.isInstanceOf[TypeKey]))
  }

  class VariableNormalizer {
    private val varMap: MutableMap[TypeTree, Seq[T]] = MutableMap.empty
    private val varSet: MutableSet[T]                = MutableSet.empty

    def normalize(ids: Seq[Identifier]): Seq[T] = {
      val mapping = ids.groupBy(id => bestRealType(id.getType)).flatMap { case (tpe, idst) =>
        val prev = varMap.get(tpe) match {
          case Some(seq) => seq
          case None => Seq.empty
        }

        if (prev.size >= idst.size) {
          idst zip prev.take(idst.size)
        } else {
          val (handled, newIds) = idst.splitAt(prev.size)
          val uIds = newIds.map(id => id -> encoder.encodeId(id))

          varMap(tpe) = prev ++ uIds.map(_._2)
          varSet ++= uIds.map(_._2)

          (handled zip prev) ++ uIds
        }
      }.toMap

      ids.map(mapping)
    }

    def normalSubst(qs: Seq[(Identifier, T)]): Map[T, T] = {
      (qs.map(_._2) zip normalize(qs.map(_._1))).toMap
    }

    def contains(idT: T): Boolean = varSet(idT)
    def get(tpe: TypeTree): Option[Seq[T]] = varMap.get(tpe)
  }

  private val abstractNormalizer = new VariableNormalizer
  private val concreteNormalizer = new VariableNormalizer

  def isQuantifier(idT: T): Boolean = abstractNormalizer.contains(idT)

  override def assumptions: Seq[T] = super.assumptions ++
    quantifications.collect { case q: Quantification => q.currentQ2Var }.toSeq

  def typeInstantiations: Map[TypeTree, Matchers] = instCtx.map.instantiations.collect {
    case (TypeKey(tpe), matchers) => tpe -> matchers
  }

  def lambdaInstantiations: Map[Lambda, Matchers] = instCtx.map.instantiations.collect {
    case (LambdaKey(lambda, tpe), matchers) => lambda -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  def partialInstantiations: Map[T, Matchers] = instCtx.map.instantiations.collect {
    case (CallerKey(caller, tpe), matchers) => caller -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  private def maxDepth(m: Matcher[T]): Int = 1 + (0 +: m.args.map {
    case Right(ma) => maxDepth(ma)
    case _ => 0
  }).max

  private def totalDepth(m: Matcher[T]): Int = 1 + m.args.map {
    case Right(ma) => totalDepth(ma)
    case _ => 0
  }.sum

  private def encodeEnablers(es: Set[T]): T =
    if (es.isEmpty) trueT else encoder.mkAnd(es.toSeq.sortBy(_.toString) : _*)

  private type Matchers = Set[(T, Matcher[T])]

  private class Context private(ctx: Map[Matcher[T], Set[Set[T]]]) extends Iterable[(Set[T], Matcher[T])] {
    def this() = this(Map.empty)

    def apply(p: (Set[T], Matcher[T])): Boolean = ctx.get(p._2) match {
      case None => false
      case Some(blockerSets) => blockerSets(p._1) || blockerSets.exists(set => set.subsetOf(p._1))
    }

    def +(p: (Set[T], Matcher[T])): Context = if (apply(p)) this else {
      val prev = ctx.getOrElse(p._2, Set.empty)
      val newSet = prev.filterNot(set => p._1.subsetOf(set)).toSet + p._1
      new Context(ctx + (p._2 -> newSet))
    }

    def ++(that: Context): Context = that.foldLeft(this)((ctx, p) => ctx + p)

    def iterator = ctx.toSeq.flatMap { case (m, bss) => bss.map(bs => bs -> m) }.iterator
    def toMatchers: Matchers = this.map(p => encodeEnablers(p._1) -> p._2).toSet
  }

  private class ContextMap(
    private var tpeMap: MutableMap[TypeTree, Context]   = MutableMap.empty,
    private var funMap: MutableMap[MatcherKey, Context] = MutableMap.empty
  ) extends IncrementalState {
    private val stack = new MutableStack[(MutableMap[TypeTree, Context], MutableMap[MatcherKey, Context])]

    def clear(): Unit = {
      stack.clear()
      tpeMap.clear()
      funMap.clear()
    }

    def reset(): Unit = clear()

    def push(): Unit = {
      stack.push((tpeMap, funMap))
      tpeMap = tpeMap.clone
      funMap = funMap.clone
    }

    def pop(): Unit = {
      val (ptpeMap, pfunMap) = stack.pop()
      tpeMap = ptpeMap
      funMap = pfunMap
    }

    def +=(p: (Set[T], Matcher[T])): Unit = matcherKey(p._2.caller, p._2.tpe) match {
      case TypeKey(tpe) => tpeMap(tpe) = tpeMap.getOrElse(tpe, new Context) + p
      case key => funMap(key) = funMap.getOrElse(key, new Context) + p
    }

    def merge(that: ContextMap): this.type = {
      for ((tpe, values) <- that.tpeMap) tpeMap(tpe) = tpeMap.getOrElse(tpe, new Context) ++ values
      for ((caller, values) <- that.funMap) funMap(caller) = funMap.getOrElse(caller, new Context) ++ values
      this
    }

    def get(caller: T, tpe: TypeTree): Context =
      funMap.getOrElse(matcherKey(caller, tpe), new Context) ++ tpeMap.getOrElse(tpe, new Context)

    def get(key: MatcherKey): Context = key match {
      case TypeKey(tpe) => tpeMap.getOrElse(tpe, new Context)
      case key => funMap.getOrElse(key, new Context) ++ tpeMap.getOrElse(key.tpe, new Context)
    }

    def instantiations: Map[MatcherKey, Matchers] =
      (funMap.toMap ++ tpeMap.map { case (tpe,ms) => TypeKey(tpe) -> ms }).mapValues(_.toMatchers)
  }

  private class InstantiationContext private (
    private var _instantiated : Context, val map : ContextMap
  ) extends IncrementalState {

    private val stack = new MutableStack[Context]

    def this() = this(new Context, new ContextMap)

    def clear(): Unit = {
      stack.clear()
      map.clear()
      _instantiated = new Context
    }

    def reset(): Unit = clear()

    def push(): Unit = {
      stack.push(_instantiated)
      map.push()
    }

    def pop(): Unit = {
      _instantiated = stack.pop()
      map.pop()
    }

    def instantiated: Context = _instantiated
    def apply(p: (Set[T], Matcher[T])): Boolean = _instantiated(p)

    def corresponding(m: Matcher[T]): Context = map.get(m.caller, m.tpe)

    def instantiate(blockers: Set[T], matcher: Matcher[T])(qs: MatcherQuantification*): Instantiation[T] = {
      if (this(blockers -> matcher)) {
        Instantiation.empty[T]
      } else {
        map += (blockers -> matcher)
        _instantiated += (blockers -> matcher)
        var instantiation = Instantiation.empty[T]
        for (q <- qs) instantiation ++= q.instantiate(blockers, matcher)
        instantiation
      }
    }

    def merge(that: InstantiationContext): this.type = {
      _instantiated ++= that._instantiated
      map.merge(that.map)
      this
    }
  }

  private[solvers] trait MatcherQuantification {
    val pathVar: (Identifier, T)
    val quantifiers: Seq[(Identifier, T)]
    val matchers: Set[Matcher[T]]
    val allMatchers: Map[T, Set[Matcher[T]]]
    val condVars: Map[Identifier, T]
    val exprVars: Map[Identifier, T]
    val condTree: Map[Identifier, Set[Identifier]]
    val clauses: Seq[T]
    val blockers: Map[T, Set[TemplateCallInfo[T]]]
    val applications: Map[T, Set[App[T]]]
    val lambdas: Seq[LambdaTemplate[T]]

    val holds: T
    val body: Expr

    lazy val quantified: Set[T] = quantifiers.map(_._2).toSet
    lazy val start = pathVar._2

    private lazy val depth = matchers.map(maxDepth).max
    private lazy val transMatchers: Set[Matcher[T]] = (for {
      (b, ms) <- allMatchers.toSeq
      m <- ms if !matchers(m) && maxDepth(m) <= depth
    } yield m).toSet

    /* Build a mapping from applications in the quantified statement to all potential concrete
     * applications previously encountered. Also make sure the current `app` is in the mapping
     * as other instantiations have been performed previously when the associated applications
     * were first encountered.
     */
    private def mappings(bs: Set[T], matcher: Matcher[T]): Set[Set[(Set[T], Matcher[T], Matcher[T])]] = {
      /* 1. select an application in the quantified proposition for which the current app can
       *    be bound when generating the new constraints
       */
      matchers.filter(qm => correspond(qm, matcher))

      /* 2. build the instantiation mapping associated to the chosen current application binding */
        .flatMap { bindingMatcher =>

      /* 2.1. select all potential matches for each quantified application */
          val matcherToInstances = matchers
            .map(qm => if (qm == bindingMatcher) {
              bindingMatcher -> Set(bs -> matcher)
            } else {
              qm -> instCtx.corresponding(qm)
            }).toMap

      /* 2.2. based on the possible bindings for each quantified application, build a set of
       *      instantiation mappings that can be used to instantiate all necessary constraints
       */
          val allMappings = matcherToInstances.foldLeft[Set[Set[(Set[T], Matcher[T], Matcher[T])]]](Set(Set.empty)) {
            case (mappings, (qm, instances)) => Set(instances.toSeq.flatMap {
              case (bs, m) => mappings.map(mapping => mapping + ((bs, qm, m)))
            } : _*)
          }

          allMappings
        }
    }

    private def extractSubst(mapping: Set[(Set[T], Matcher[T], Matcher[T])]): (Set[T], Map[T,Arg[T]], Boolean) = {
      var constraints: Set[T] = Set.empty
      var eqConstraints: Set[(T, T)] = Set.empty
      var subst: Map[T, Arg[T]] = Map.empty

      var matcherEqs: Set[(T, T)] = Set.empty
      def strictnessCnstr(qarg: Arg[T], arg: Arg[T]): Unit = (qarg, arg) match {
        case (Right(qam), Right(am)) => (qam.args zip am.args).foreach(p => strictnessCnstr(p._1, p._2))
        case _ => matcherEqs += qarg.encoded -> arg.encoded
      }

      for {
        (bs, qm @ Matcher(qcaller, _, qargs, _), m @ Matcher(caller, _, args, _)) <- mapping
        _ = constraints ++= bs
        (qarg, arg) <- (qargs zip args)
        _ = strictnessCnstr(qarg, arg)
      } qarg match {
        case Left(quant) if !quantified(quant) || subst.isDefinedAt(quant) =>
          eqConstraints += (quant -> arg.encoded)
        case Left(quant) if quantified(quant) =>
          subst += quant -> arg
        case Right(qam) =>
          eqConstraints += (qam.encoded -> arg.encoded)
      }

      val substituter = encoder.substitute(subst.mapValues(_.encoded))
      val substConstraints = constraints.filter(_ != trueT).map(substituter)
      val substEqs = eqConstraints.map(p => substituter(p._1) -> p._2)
        .filter(p => p._1 != p._2).map(p => encoder.mkEquals(p._1, p._2))
      val enablers = substConstraints ++ substEqs
      val isStrict = matcherEqs.forall(p => substituter(p._1) == p._2)

      (enablers, subst, isStrict)
    }

    def instantiate(bs: Set[T], matcher: Matcher[T]): Instantiation[T] = {
      var instantiation = Instantiation.empty[T]

      for (mapping <- mappings(bs, matcher)) {
        val (enablers, subst, isStrict) = extractSubst(mapping)

        if (!skip(subst)) {
          if (!isStrict) {
            val msubst = subst.collect { case (c, Right(m)) => c -> m }
            val substituter = encoder.substitute(subst.mapValues(_.encoded))
            ignoredSubsts(this) += ((currentGen + 3, enablers, subst))
          } else {
            instantiation ++= instantiateSubst(enablers, subst, strict = true)
          }
        }
      }

      instantiation
    }

    def instantiateSubst(enablers: Set[T], subst: Map[T, Arg[T]], strict: Boolean = false): Instantiation[T] = {
      if (handledSubsts(this)(enablers -> subst)) {
        Instantiation.empty[T]
      } else {
        handledSubsts(this) += enablers -> subst

        var instantiation = Instantiation.empty[T]
        val (enabler, optEnabler) = freshBlocker(enablers)
        if (optEnabler.isDefined) {
          instantiation = instantiation withClause encoder.mkEquals(enabler, optEnabler.get)
        }

        val baseSubst = subst ++ instanceSubst(enabler).mapValues(Left(_))
        val (substMap, inst) = Template.substitution[T](encoder, QuantificationManager.this,
          condVars, exprVars, condTree, Seq.empty, lambdas, Set.empty, baseSubst, pathVar._1, enabler)
        instantiation ++= inst

        val msubst = substMap.collect { case (c, Right(m)) => c -> m }
        val substituter = encoder.substitute(substMap.mapValues(_.encoded))
        registerBlockers(substituter)

        instantiation ++= Template.instantiate(encoder, QuantificationManager.this,
          clauses, blockers, applications, Map.empty, substMap)

        for ((b,ms) <- allMatchers; m <- ms) {
          val sb = enablers ++ (if (b == start) Set.empty else Set(substituter(b)))
          val sm = m.substitute(substituter, msubst)

          if (strict && (matchers(m) || transMatchers(m))) {
            instantiation ++= instCtx.instantiate(sb, sm)(quantifications.toSeq : _*)
          } else if (!matchers(m)) {
            ignoredMatchers += ((currentGen + 2 + totalDepth(m), sb, sm))
          }
        }

        instantiation
      }
    }

    protected def instanceSubst(enabler: T): Map[T, T]

    protected def skip(subst: Map[T, Arg[T]]): Boolean = false

    protected def registerBlockers(substituter: T => T): Unit = ()
  }

  private class Quantification (
    val pathVar: (Identifier, T),
    val qs: (Identifier, T),
    val q2s: (Identifier, T),
    val insts: (Identifier, T),
    val guardVar: T,
    val quantifiers: Seq[(Identifier, T)],
    val matchers: Set[Matcher[T]],
    val allMatchers: Map[T, Set[Matcher[T]]],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val condTree: Map[Identifier, Set[Identifier]],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Seq[LambdaTemplate[T]],
    val template: QuantificationTemplate[T]) extends MatcherQuantification {

    private var _currentQ2Var: T = qs._2
    def currentQ2Var = _currentQ2Var
    val holds = qs._2
    val body = template.forall.body

    private var _currentInsts: Map[T, Set[T]] = Map.empty
    def currentInsts = _currentInsts

    protected def instanceSubst(enabler: T): Map[T, T] = {
      val nextQ2Var = encoder.encodeId(q2s._1)

      val subst = Map(qs._2 -> currentQ2Var, guardVar -> enabler,
        q2s._2 -> nextQ2Var, insts._2 -> encoder.encodeId(insts._1))

      _currentQ2Var = nextQ2Var
      subst
    }

    override def registerBlockers(substituter: T => T): Unit = {
      val freshInst = substituter(insts._2)
      val bs = (blockers.keys ++ applications.keys).map(substituter).toSet
      _currentInsts += freshInst -> bs
    }
  }

  private lazy val blockerId = FreshIdentifier("blocker", BooleanType, true)
  private lazy val enablersToBlocker: MutableMap[Set[T], T] = MutableMap.empty
  private lazy val blockerToEnablers: MutableMap[T, Set[T]] = MutableMap.empty
  private def freshBlocker(enablers: Set[T]): (T, Option[T]) = enablers.toSeq match {
    case Seq(b) if isBlocker(b) => (b, None)
    case _ =>
      val last = enablersToBlocker.get(enablers).orElse {
        val initialEnablers = enablers.flatMap(e => blockerToEnablers.getOrElse(e, Set(e)))
        enablersToBlocker.get(initialEnablers)
      }

      last match {
        case Some(b) => (b, None)
        case None =>
          val nb = encoder.encodeId(blockerId)
          enablersToBlocker += enablers -> nb
          blockerToEnablers += nb -> enablers
          for (b <- enablers if isBlocker(b)) implies(b, nb)
          blocker(nb)

          (nb, Some(encodeEnablers(enablers)))
      }
  }

  private class LambdaAxiom (
    val pathVar: (Identifier, T),
    val blocker: T,
    val guardVar: T,
    val quantifiers: Seq[(Identifier, T)],
    val matchers: Set[Matcher[T]],
    val allMatchers: Map[T, Set[Matcher[T]]],
    val condVars: Map[Identifier, T],
    val exprVars: Map[Identifier, T],
    val condTree: Map[Identifier, Set[Identifier]],
    val clauses: Seq[T],
    val blockers: Map[T, Set[TemplateCallInfo[T]]],
    val applications: Map[T, Set[App[T]]],
    val lambdas: Seq[LambdaTemplate[T]],
    val template: LambdaTemplate[T]) extends MatcherQuantification {

    val holds = start
    val body = template.lambda.body

    protected def instanceSubst(enabler: T): Map[T, T] = {
      Map(guardVar -> start, blocker -> enabler)
    }

    override protected def skip(subst: Map[T, Arg[T]]): Boolean = {
      val substituter = encoder.substitute(subst.mapValues(_.encoded))
      val msubst = subst.collect { case (c, Right(m)) => c -> m }
      allMatchers.forall { case (b, ms) =>
        ms.forall(m => matchers(m) || instCtx(Set(substituter(b)) -> m.substitute(substituter, msubst)))
      }
    }
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

  def instantiateAxiom(template: LambdaTemplate[T], substMap: Map[T, Arg[T]]): Instantiation[T] = {
    def quantifiedMatcher(m: Matcher[T]): Boolean = m.args.exists(a => a match {
      case Left(v) => isQuantifier(v)
      case Right(m) => quantifiedMatcher(m)
    })

    val quantified = template.arguments flatMap {
      case (id, idT) => substMap(idT) match {
        case Left(v) if isQuantifier(v) => Some(id)
        case Right(m) if quantifiedMatcher(m) => Some(id)
        case _ => None
      }
    }

    val quantifiers = quantified zip abstractNormalizer.normalize(quantified)
    val key = template.structure -> quantifiers

    if (quantifiers.isEmpty || lambdaAxioms(key)) {
      Instantiation.empty[T]
    } else {
      lambdaAxioms += key
      val blockerT = encoder.encodeId(blockerId)

      val guard = FreshIdentifier("guard", BooleanType, true)
      val guardT = encoder.encodeId(guard)

      val substituter = encoder.substitute(substMap.mapValues(_.encoded) + (template.start -> blockerT))
      val msubst = substMap.collect { case (c, Right(m)) => c -> m }

      val allMatchers = template.matchers map { case (b, ms) =>
        substituter(b) -> ms.map(_.substitute(substituter, msubst))
      }

      val qMatchers = allMatchers.flatMap(_._2).toSet

      val encArgs = template.args map (arg => Left(arg).substitute(substituter, msubst))
      val app = Application(Variable(template.ids._1), template.arguments.map(_._1.toVariable))
      val appT = encoder.encodeExpr((template.arguments.map(_._1) zip encArgs.map(_.encoded)).toMap + template.ids)(app)
      val selfMatcher = Matcher(template.ids._2, template.tpe, encArgs, appT)

      val instMatchers = allMatchers + (template.start -> (allMatchers.getOrElse(template.start, Set.empty) + selfMatcher))

      val enablingClause = encoder.mkImplies(guardT, blockerT)

      val condVars = template.condVars map { case (id, idT) => id -> substituter(idT) }
      val exprVars = template.exprVars map { case (id, idT) => id -> substituter(idT) }
      val clauses = (template.clauses map substituter) :+ enablingClause
      val blockers = template.blockers map { case (b, fis) =>
        substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(_.substitute(substituter, msubst))))
      }

      val applications = template.applications map { case (b, apps) =>
        substituter(b) -> apps.map(app => app.copy(
          caller = substituter(app.caller),
          args = app.args.map(_.substitute(substituter, msubst))
        ))
      }

      val lambdas = template.lambdas map (_.substitute(substituter, msubst))

      val quantified = quantifiers.map(_._2).toSet
      val matchQuorums = extractQuorums(quantified, qMatchers, lambdas)

      var instantiation = Instantiation.empty[T]

      for (matchers <- matchQuorums) {
        val axiom = new LambdaAxiom(template.pathVar._1 -> substituter(template.start),
          blockerT, guardT, quantifiers, matchers, instMatchers, condVars, exprVars, template.condTree,
          clauses, blockers, applications, lambdas, template)

        quantifications += axiom
        handledSubsts += axiom -> MutableSet.empty
        ignoredSubsts += axiom -> MutableSet.empty

        val newCtx = new InstantiationContext()
        for ((b,m) <- instCtx.instantiated) {
          instantiation ++= newCtx.instantiate(b, m)(axiom)
        }
        instCtx.merge(newCtx)
      }

      instantiation ++= instantiateConstants(quantifiers, qMatchers)

      instantiation
    }
  }

  def instantiateQuantification(template: QuantificationTemplate[T]): (T, Instantiation[T]) = {
    templates.get(template.key) match {
      case Some(idT) =>
        (idT, Instantiation.empty)

      case None =>
        val qT = encoder.encodeId(template.qs._1)
        val quantified = template.quantifiers.map(_._2).toSet
        val matcherSet = template.matchers.flatMap(_._2).toSet
        val matchQuorums = extractQuorums(quantified, matcherSet, template.lambdas)

        var instantiation = Instantiation.empty[T]

        val qs = for (matchers <- matchQuorums) yield {
          val newQ = encoder.encodeId(template.qs._1)
          val substituter = encoder.substitute(Map(template.qs._2 -> newQ))

          val quantification = new Quantification(
            template.pathVar,
            template.qs._1 -> newQ,
            template.q2s, template.insts, template.guardVar,
            template.quantifiers, matchers, template.matchers,
            template.condVars, template.exprVars, template.condTree,
            template.clauses map substituter, // one clause depends on 'q' (and therefore 'newQ')
            template.blockers, template.applications, template.lambdas, template)

          quantifications += quantification
          handledSubsts += quantification -> MutableSet.empty
          ignoredSubsts += quantification -> MutableSet.empty

          val newCtx = new InstantiationContext()
          for ((b,m) <- instCtx.instantiated) {
            instantiation ++= newCtx.instantiate(b, m)(quantification)
          }
          instCtx.merge(newCtx)

          quantification.qs._2
        }

        instantiation = instantiation withClause {
          val newQs =
            if (qs.isEmpty) trueT
            else if (qs.size == 1) qs.head
            else encoder.mkAnd(qs : _*)
          encoder.mkImplies(template.start, encoder.mkEquals(qT, newQs))
        }

        instantiation ++= instantiateConstants(template.quantifiers, matcherSet)

        templates += template.key -> qT
        (qT, instantiation)
    }
  }

  def instantiateMatcher(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
    instCtx.instantiate(Set(blocker), matcher)(quantifications.toSeq : _*)
  }

  def hasIgnored: Boolean = ignoredSubsts.nonEmpty || ignoredMatchers.nonEmpty

  def instantiateIgnored(force: Boolean = false): Instantiation[T] = {
    currentGen = if (!force) currentGen + 1 else {
      val gens = ignoredSubsts.toSeq.flatMap(_._2).map(_._1) ++ ignoredMatchers.toSeq.map(_._1)
      if (gens.isEmpty) currentGen else gens.min
    }

    var instantiation = Instantiation.empty[T]

    val matchersToRelease = ignoredMatchers.toList.flatMap { case e @ (gen, b, m) =>
      if (gen == currentGen) {
        ignoredMatchers -= e
        Some(b -> m)
      } else {
        None
      }
    }

    for ((bs,m) <- matchersToRelease) {
      instantiation ++= instCtx.instantiate(bs, m)(quantifications.toSeq : _*)
    }

    val substsToRelease = quantifications.toList.flatMap { q =>
      val qsubsts = ignoredSubsts(q)
      qsubsts.toList.flatMap { case e @ (gen, enablers, subst) =>
        if (gen == currentGen) {
          qsubsts -= e
          Some((q, enablers, subst))
        } else {
          None
        }
      }
    }

    for ((q, enablers, subst) <- substsToRelease) {
      instantiation ++= q.instantiateSubst(enablers, subst, strict = false)
    }

    instantiation
  }

  private def instantiateConstants(quantifiers: Seq[(Identifier, T)], matchers: Set[Matcher[T]]): Instantiation[T] = {
    var instantiation: Instantiation[T] = Instantiation.empty

    for (normalizer <- List(abstractNormalizer, concreteNormalizer)) {
      val quantifierSubst = normalizer.normalSubst(quantifiers)
      val substituter = encoder.substitute(quantifierSubst)

      for {
        m <- matchers
        sm = m.substitute(substituter, Map.empty)
        if !instCtx.corresponding(sm).exists(_._2.args == sm.args)
      } instantiation ++= instCtx.instantiate(Set.empty, sm)(quantifications.toSeq : _*)

      def unifyMatchers(matchers: Seq[Matcher[T]]): Instantiation[T] = matchers match {
        case sm +: others =>
          var instantiation = Instantiation.empty[T]
          for (pm <- others if correspond(pm, sm)) {
            val encodedArgs = (sm.args zip pm.args).map(p => p._1.encoded -> p._2.encoded)
            val mismatches = encodedArgs.zipWithIndex.collect {
              case ((sa, pa), idx) if isQuantifier(sa) && isQuantifier(pa) && sa != pa => (idx, (pa, sa))
            }.toMap

            def extractChains(indexes: Seq[Int], partials: Seq[Seq[Int]]): Seq[Seq[Int]] = indexes match {
              case idx +: xs =>
                val (p1, p2) = mismatches(idx)
                val newPartials = Seq(idx) +: partials.map { seq =>
                  if (mismatches(seq.head)._1 == p2) idx +: seq
                  else if (mismatches(seq.last)._2 == p1) seq :+ idx
                  else seq
                }

                val (closed, remaining) = newPartials.partition { seq =>
                  mismatches(seq.head)._1 == mismatches(seq.last)._2
                }
                closed ++ extractChains(xs, partials ++ remaining)

              case _ => Seq.empty
            }

            val chains = extractChains(mismatches.keys.toSeq, Seq.empty)
            val positions = chains.foldLeft(Map.empty[Int, Int]) { (mapping, seq) =>
              val res = seq.min
              mapping ++ seq.map(i => i -> res)
            }

            def extractArgs(args: Seq[Arg[T]]): Seq[Arg[T]] =
              (0 until args.size).map(i => args(positions.getOrElse(i, i)))

            instantiation ++= instCtx.instantiate(Set.empty, sm.copy(args = extractArgs(sm.args)))(quantifications.toSeq : _*)
            instantiation ++= instCtx.instantiate(Set.empty, pm.copy(args = extractArgs(pm.args)))(quantifications.toSeq : _*)
          }

          instantiation ++ unifyMatchers(others)

        case _ => Instantiation.empty[T]
      }

      if (normalizer == abstractNormalizer) {
        val substMatchers = matchers.map(_.substitute(substituter, Map.empty))
        instantiation ++= unifyMatchers(substMatchers.toSeq)
      }
    }

    instantiation
  }

  def checkClauses: Seq[T] = {
    val clauses = new scala.collection.mutable.ListBuffer[T]
    val keyClause = MutableMap.empty[MatcherKey, (Seq[T], T)]

    for ((_, bs, m) <- ignoredMatchers) {
      val key = matcherKey(m.caller, m.tpe)
      val QTM(argTypes, _) = key.tpe

      val (values, clause) = keyClause.getOrElse(key, {
        val insts = instCtx.map.get(key).toMatchers

        val guard = FreshIdentifier("guard", BooleanType)
        val elems = argTypes.map(tpe => FreshIdentifier("elem", tpe))
        val values = argTypes.map(tpe => FreshIdentifier("value", tpe))
        val expr = andJoin(Variable(guard) +: (elems zip values).map(p => Equals(Variable(p._1), Variable(p._2))))

        val guardP = guard -> encoder.encodeId(guard)
        val elemsP = elems.map(e => e -> encoder.encodeId(e))
        val valuesP = values.map(v => v -> encoder.encodeId(v))
        val exprT = encoder.encodeExpr(elemsP.toMap ++ valuesP + guardP)(expr)

        val disjuncts = insts.toSeq.map { case (b, im) =>
          val bp = if (m.caller != im.caller) encoder.mkAnd(encoder.mkEquals(m.caller, im.caller), b) else b
          val subst = (elemsP.map(_._2) zip im.args.map(_.encoded)).toMap + (guardP._2 -> bp)
          encoder.substitute(subst)(exprT)
        }

        val res = (valuesP.map(_._2), encoder.mkOr(disjuncts : _*))
        keyClause += key -> res
        res
      })

      val b = encodeEnablers(bs)
      val substMap = (values zip m.args.map(_.encoded)).toMap
      clauses += encoder.substitute(substMap)(encoder.mkImplies(b, clause))
    }

    for (q <- quantifications) {
      val guard = FreshIdentifier("guard", BooleanType)
      val elems = q.quantifiers.map(_._1)
      val values = elems.map(id => id.freshen)
      val expr = andJoin(Variable(guard) +: (elems zip values).map(p => Equals(Variable(p._1), Variable(p._2))))

      val guardP = guard -> encoder.encodeId(guard)
      val elemsP = elems.map(e => e -> encoder.encodeId(e))
      val valuesP = values.map(v => v -> encoder.encodeId(v))
      val exprT = encoder.encodeExpr(elemsP.toMap ++ valuesP + guardP)(expr)

      val disjunction = handledSubsts(q) match {
        case set if set.isEmpty => encoder.encodeExpr(Map.empty)(BooleanLiteral(false))
        case set => encoder.mkOr(set.toSeq.map { case (enablers, subst) =>
          val b = if (enablers.isEmpty) trueT else encoder.mkAnd(enablers.toSeq : _*)
          val substMap = (elemsP.map(_._2) zip q.quantifiers.map(p => subst(p._2).encoded)).toMap + (guardP._2 -> b)
          encoder.substitute(substMap)(exprT)
        } : _*)
      }

      for ((_, enablers, subst) <- ignoredSubsts(q)) {
        val b = if (enablers.isEmpty) trueT else encoder.mkAnd(enablers.toSeq : _*)
        val substMap = (valuesP.map(_._2) zip q.quantifiers.map(p => subst(p._2).encoded)).toMap
        clauses += encoder.substitute(substMap)(encoder.mkImplies(b, disjunction))
      }
    }

    def isQuantified(e: Arg[T]): Boolean = e match {
      case Left(t) => isQuantifier(t)
      case Right(m) => m.args.exists(isQuantified)
    }

    for ((key, ctx) <- instCtx.map.instantiations) {
      val QTM(argTypes, _) = key.tpe

      for {
        (tpe, idx) <- argTypes.zipWithIndex
        quants <- abstractNormalizer.get(tpe) if quants.nonEmpty
        (b, m) <- ctx
        arg = m.args(idx) if !isQuantified(arg)
      } clauses += encoder.mkAnd(quants.map(q => encoder.mkNot(encoder.mkEquals(q, arg.encoded))) : _*)

      val byPosition: Iterable[Seq[T]] = ctx.flatMap { case (b, m) =>
        if (b != trueT) Seq.empty else m.args.zipWithIndex
      }.groupBy(_._2).map(p => p._2.toSeq.flatMap {
        case (a, _) => if (isQuantified(a)) Some(a.encoded) else None
      }).filter(_.nonEmpty)

      for ((a +: as) <- byPosition; a2 <- as) {
        clauses += encoder.mkEquals(a, a2)
      }
    }

    clauses.toSeq
  }

  trait ModelView {
    protected val vars: Map[Identifier, T]
    protected val evaluator: evaluators.DeterministicEvaluator

    protected def get(id: Identifier): Option[Expr]
    protected def eval(elem: T, tpe: TypeTree): Option[Expr]

    implicit lazy val context = evaluator.context
    lazy val reporter = context.reporter

    private def extract(b: T, m: Matcher[T]): Option[Seq[Expr]] = {
      val QTM(fromTypes, _) = m.tpe
      val optEnabler = eval(b, BooleanType)
      optEnabler.filter(_ == BooleanLiteral(true)).flatMap { _ =>
        val optArgs = (m.args zip fromTypes).map { case (arg, tpe) => eval(arg.encoded, tpe) }
        if (optArgs.forall(_.isDefined)) Some(optArgs.map(_.get))
        else None
      }
    }

    private def functionsOf(expr: Expr, path: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = {

      def reconstruct(subs: Seq[(Seq[(Expr, Expr)], Seq[Expr] => Expr)],
                      recons: Seq[Expr] => Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) =
        (subs.flatMap(_._1), (exprs: Seq[Expr]) => {
          var curr = exprs
          recons(subs.map { case (es, recons) =>
            val (used, remaining) = curr.splitAt(es.size)
            curr = remaining
            recons(used)
          })
        })

      def rec(expr: Expr, path: Expr): (Seq[(Expr, Expr)], Seq[Expr] => Expr) = expr match {
        case (_: Lambda) | (_: FiniteLambda) =>
          (Seq(expr -> path), (es: Seq[Expr]) => es.head)

        case Tuple(es) => reconstruct(es.zipWithIndex.map {
          case (e, i) => rec(e, TupleSelect(path, i + 1))
        }, Tuple)

        case CaseClass(cct, es) => reconstruct((cct.classDef.fieldsIds zip es).map {
          case (id, e) => rec(e, CaseClassSelector(cct, path, id))
        }, CaseClass(cct, _))

        case _ => (Seq.empty, (es: Seq[Expr]) => expr)
      }

      rec(expr, path)
    }

    def getPartialModel: PartialModel = {
      val typeDomains: Map[TypeTree, Set[Seq[Expr]]] = typeInstantiations.map {
        case (tpe, domain) => tpe -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
      }

      val lambdaDomains: Map[Lambda, Set[Seq[Expr]]] = lambdaInstantiations.map {
        case (l, domain) => l -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
      }

      val domains = new Domains(lambdaDomains, typeDomains)

      val partialDomains: Map[T, Set[Seq[Expr]]] = partialInstantiations.map {
        case (t, domain) => t -> domain.flatMap { case (b, m) => extract(b, m) }.toSet
      }

      def extractElse(body: Expr): Expr = body match {
        case IfExpr(cond, thenn, elze) => extractElse(elze)
        case _ => body
      }

      val mapping = vars.map { case (id, idT) =>
        val value = get(id).getOrElse(simplestValue(id.getType))
        val (functions, recons) = functionsOf(value, Variable(id))

        id -> recons(functions.map { case (f, path) =>
          val encoded = encoder.encodeExpr(Map(id -> idT))(path)
          val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
          partialDomains.get(encoded).orElse(typeDomains.get(tpe)).map { domain =>
            FiniteLambda(domain.toSeq.map { es =>
              val optEv = evaluator.eval(application(f, es)).result
              es -> optEv.getOrElse(scala.sys.error("Unexpectedly failed to evaluate " + application(f, es)))
            }, f match {
              case FiniteLambda(_, dflt, _) => dflt
              case Lambda(_, body) => extractElse(body)
              case _ => scala.sys.error("What kind of function is this : " + f.asString + " !?")
            }, tpe)
          }.getOrElse(f)
        })
      }

      new PartialModel(mapping, domains)
    }

    def getTotalModel: Model = {

      def checkForalls(quantified: Set[Identifier], body: Expr): Option[String] = {
        val matchers = purescala.ExprOps.collect[(Expr, Seq[Expr])] {
          case QM(e, args) => Set(e -> args)
          case _ => Set.empty
        } (body)

        if (matchers.isEmpty)
          return Some("No matchers found.")

        val matcherToQuants = matchers.foldLeft(Map.empty[Expr, Set[Identifier]]) {
          case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
            case Variable(id) if quantified(id) => Set(id)
            case _ => Set.empty[Identifier]
          }))
        }

        val bijectiveMappings = matcherToQuants.filter(_._2.nonEmpty).groupBy(_._2)
        if (bijectiveMappings.size > 1)
          return Some("Non-bijective mapping for symbol " + bijectiveMappings.head._2.head._1.asString)

        def quantifiedArg(e: Expr): Boolean = e match {
          case Variable(id) => quantified(id)
          case QM(_, args) => args.forall(quantifiedArg)
          case _ => false
        }

        purescala.ExprOps.postTraversal(m => m match {
          case QM(_, args) =>
            val qArgs = args.filter(quantifiedArg)

            if (qArgs.nonEmpty && qArgs.size < args.size)
              return Some("Mixed ground and quantified arguments in " + m.asString)

          case Operator(es, _) if es.collect { case Variable(id) if quantified(id) => id }.nonEmpty =>
            return Some("Invalid operation on quantifiers " + m.asString)

          case (_: Equals) | (_: And) | (_: Or) | (_: Implies) | (_: Not) => // OK

          case Operator(es, _) if (es.flatMap(variablesOf).toSet & quantified).nonEmpty =>
            return Some("Unandled implications from operation " + m.asString)

          case _ =>
        }) (body)

        body match {
          case Variable(id) if quantified(id) =>
            Some("Unexpected free quantifier " + id.asString)
          case _ => None
        }
      }

      val issues: Iterable[(Seq[Identifier], Expr, String)] = for {
        q <- quantifications.view
        if eval(q.holds, BooleanType) == Some(BooleanLiteral(true))
        msg <- checkForalls(q.quantifiers.map(_._1).toSet, q.body)
      } yield (q.quantifiers.map(_._1), q.body, msg)

      if (issues.nonEmpty) {
        val (quantifiers, body, msg) = issues.head
        reporter.warning("Model soundness not guaranteed for \u2200" +
          quantifiers.map(_.asString).mkString(",") + ". " + body.asString+" :\n => " + msg)
      }

      val types = typeInstantiations
      val partials = partialInstantiations

      def extractCond(params: Seq[Identifier], args: Seq[(T, Expr)], structure: Map[T, Identifier]): Seq[Expr] = (params, args) match {
        case (id +: rparams, (v, arg) +: rargs) =>
          if (isQuantifier(v)) {
            structure.get(v) match {
              case Some(pid) => Equals(Variable(id), Variable(pid)) +: extractCond(rparams, rargs, structure)
              case None => extractCond(rparams, rargs, structure + (v -> id))
            }
          } else {
            Equals(Variable(id), arg) +: extractCond(rparams, rargs, structure)
          }
        case _ => Seq.empty
      }

      new Model(vars.map { case (id, idT) =>
        val value = get(id).getOrElse(simplestValue(id.getType))
        val (functions, recons) = functionsOf(value, Variable(id))

        id -> recons(functions.map { case (f, path) =>
          val encoded = encoder.encodeExpr(Map(id -> idT))(path)
          val tpe = bestRealType(f.getType).asInstanceOf[FunctionType]
          val params = tpe.from.map(tpe => FreshIdentifier("x", tpe, true))
          partials.get(encoded).orElse(types.get(tpe)).map { domain =>
            val conditionals = domain.flatMap { case (b, m) =>
              extract(b, m).map { args =>
                val result = evaluator.eval(application(f, args)).result.getOrElse {
                  scala.sys.error("Unexpectedly failed to evaluate " + application(f, args))
                }

                val cond = if (m.args.exists(arg => isQuantifier(arg.encoded))) {
                  extractCond(params, m.args.map(_.encoded) zip args, Map.empty)
                } else {
                  (params zip args).map(p => Equals(Variable(p._1), p._2))
                }

                cond -> result
              }
            }.toMap

            if (conditionals.isEmpty) f match {
              case FiniteLambda(mapping, dflt, tpe) =>
                Lambda(params.map(ValDef(_)), mapping.foldRight(dflt) { case ((es, v), elze) =>
                  IfExpr(andJoin((params zip es).map(p => Equals(p._1.toVariable, p._2))), v, elze)
                })
              case _ => f
            } else {
              val ((_, dflt)) +: rest = conditionals.toSeq.sortBy { case (conds, _) =>
                (conds.flatMap(variablesOf).toSet.size, conds.size)
              }

              val body = rest.foldLeft(dflt) { case (elze, (conds, res)) =>
                if (conds.isEmpty) elze else (elze match {
                  case pres if res == pres => res
                  case _ => IfExpr(andJoin(conds), res, elze)
                })
              }

              Lambda(params.map(ValDef(_)), body)
            }
          }.getOrElse(f)
        })
      })
    }
  }

  def getModel(vs: Map[Identifier, T], ev: DeterministicEvaluator, _get: Identifier => Option[Expr], _eval: (T, TypeTree) => Option[Expr]) = new ModelView {
    val vars: Map[Identifier, T] = vs
    val evaluator: DeterministicEvaluator = ev

    def get(id: Identifier): Option[Expr] = _get(id)
    def eval(elem: T, tpe: TypeTree): Option[Expr] = _eval(elem, tpe)
  }

  def getBlockersToPromote(eval: (T, TypeTree) => Option[Expr]): Seq[T] = quantifications.toSeq.flatMap {
    case q: Quantification if eval(q.qs._2, BooleanType) == Some(BooleanLiteral(false)) =>
      val falseInsts = q.currentInsts.filter { case (inst, bs) => eval(inst, BooleanType) == Some(BooleanLiteral(false)) }
      falseInsts.flatMap(_._2)
    case _ => Seq.empty
  }
}

