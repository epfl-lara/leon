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
import purescala.TypeOps._
import purescala.Quantification.{QuantificationTypeMatcher => QTM}

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
  val dependencies: Map[Identifier, T],
  val structuralKey: Forall) extends KeyedTemplate[T, Forall] {

  lazy val start = pathVar._2

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
      dependencies.map { case (id, value) => id -> substituter(value) },
      structuralKey
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

    val (clauses, blockers, applications, matchers, _) =
      Template.encode(encoder, pathVar, quantifiers, condVars, exprVars, guardedExprs, lambdas,
        substMap = baseSubstMap + q2s + insts + guards + qs)

    val (structuralQuant, structSubst) = normalizeStructure(proposition)
    val keyDeps = dependencies.map { case (id, idT) => structSubst(id) -> idT }
    val key = structuralQuant.asInstanceOf[Forall]

    new QuantificationTemplate[T](quantificationManager,
      pathVar, qs, q2s, insts, guards._2, quantifiers, condVars, exprVars, condTree,
      clauses, blockers, applications, matchers, lambdas, keyDeps, key)
  }
}

class QuantificationManager[T](encoder: TemplateEncoder[T]) extends LambdaManager[T](encoder) {
  private val quantifications = new IncrementalSeq[MatcherQuantification]
  private val instCtx         = new InstantiationContext

  private val ignoredMatchers = new IncrementalSeq[(Int, Set[T], Matcher[T])]
  private val ignoredSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Int, Set[T], Map[T,Arg[T]])]]
  private val handledSubsts   = new IncrementalMap[MatcherQuantification, MutableSet[(Set[T], Map[T,Arg[T]])]]

  private val known           = new IncrementalSet[T]
  private val lambdaAxioms    = new IncrementalSet[((Expr, Seq[T]), Seq[(Identifier, T)])]
  private val templates       = new IncrementalMap[(Expr, Seq[T]), T]

  override protected def incrementals: List[IncrementalState] =
    List(quantifications, instCtx, ignoredMatchers, ignoredSubsts,
      handledSubsts, known, lambdaAxioms, templates) ++ super.incrementals

  private var currentGen = 0

  private sealed abstract class MatcherKey(val tpe: TypeTree)
  private case class CallerKey(caller: T, tt: TypeTree) extends MatcherKey(tt)
  private case class LambdaKey(lambda: Lambda, tt: TypeTree) extends MatcherKey(tt)
  private case class TypeKey(tt: TypeTree) extends MatcherKey(tt)

  private def matcherKey(caller: T, tpe: TypeTree): MatcherKey = tpe match {
    case _: FunctionType if known(caller) => CallerKey(caller, tpe)
    case _: FunctionType if byID.isDefinedAt(caller) => LambdaKey(byID(caller).structuralKey, tpe)
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

  private val uniformQuantMap: MutableMap[TypeTree, Seq[T]] = MutableMap.empty
  private val uniformQuantSet: MutableSet[T]                = MutableSet.empty

  def isQuantifier(idT: T): Boolean = uniformQuantSet(idT)
  def uniformQuants(ids: Seq[Identifier]): Seq[T] = {
    val mapping = ids.groupBy(id => bestRealType(id.getType)).flatMap { case (tpe, idst) =>
      val prev = uniformQuantMap.get(tpe) match {
        case Some(seq) => seq
        case None => Seq.empty
      }

      if (prev.size >= idst.size) {
        idst zip prev.take(idst.size)
      } else {
        val (handled, newIds) = idst.splitAt(prev.size)
        val uIds = newIds.map(id => id -> encoder.encodeId(id))

        uniformQuantMap(tpe) = prev ++ uIds.map(_._2)
        uniformQuantSet ++= uIds.map(_._2)

        (handled zip prev) ++ uIds
      }
    }.toMap

    ids.map(mapping)
  }

  private def uniformSubst(qs: Seq[(Identifier, T)]): Map[T, T] = {
    (qs.map(_._2) zip uniformQuants(qs.map(_._1))).toMap
  }

  def assumptions: Seq[T] = quantifications.collect { case q: Quantification => q.currentQ2Var }.toSeq

  def typeInstantiations: Map[TypeTree, Matchers] = instCtx.map.instantiations.collect {
    case (TypeKey(tpe), matchers) => tpe -> matchers
  }

  def lambdaInstantiations: Map[Lambda, Matchers] = instCtx.map.instantiations.collect {
    case (LambdaKey(lambda, tpe), matchers) => lambda -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  def partialInstantiations: Map[T, Matchers] = instCtx.map.instantiations.collect {
    case (CallerKey(caller, tpe), matchers) => caller -> (matchers ++ instCtx.map.get(TypeKey(tpe)).toMatchers)
  }

  override def registerFree(ids: Seq[(Identifier, T)]): Unit = {
    super.registerFree(ids)
    known ++= ids.map(_._2)
  }

  private def matcherDepth(m: Matcher[T]): Int = 1 + (0 +: m.args.map {
    case Right(ma) => matcherDepth(ma)
    case _ => 0
  }).max

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
      val prev = ctx.getOrElse(p._2, Seq.empty)
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
      case key => funMap.getOrElse(key, new Context)
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

  private trait MatcherQuantification {
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

    lazy val quantified: Set[T] = quantifiers.map(_._2).toSet
    lazy val start = pathVar._2

    private lazy val depth = matchers.map(matcherDepth).max
    private lazy val transMatchers: Set[Matcher[T]] = (for {
      (b, ms) <- allMatchers.toSeq
      m <- ms if !matchers(m) && matcherDepth(m) <= depth
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

      /* 2.3. filter out bindings that don't make sense where abstract sub-matchers
       *      (matchers in arguments of other matchers) are bound to different concrete
       *      matchers in the argument and quorum positions
       */
          allMappings.filter { s =>
            def expand(ms: Traversable[(Arg[T], Arg[T])]): Set[(Matcher[T], Matcher[T])] = ms.flatMap {
              case (Right(qm), Right(m)) => Set(qm -> m) ++ expand(qm.args zip m.args)
              case _ => Set.empty[(Matcher[T], Matcher[T])]
            }.toSet

            expand(s.map(p => Right(p._2) -> Right(p._3))).groupBy(_._1).forall(_._2.size == 1)
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
        case Left(quant) if subst.isDefinedAt(quant) =>
          eqConstraints += (quant -> arg.encoded)
        case Left(quant) if quantified(quant) =>
          subst += quant -> arg
        case Right(qam) =>
          val argVal = arg.encoded
          eqConstraints += (qam.encoded -> argVal)
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
            ignoreSubst(enablers, subst)
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
        val allEnablers = fixpoint((enablers: Set[T]) => enablers.flatMap(blockerParents))(enablers)

        var instantiation = Instantiation.empty[T]
        val (enabler, optEnabler) = freshBlocker(allEnablers)
        if (optEnabler.isDefined) {
          instantiation = instantiation withClause encoder.mkEquals(enabler, optEnabler.get)
        }

        val baseSubst = subst ++ instanceSubst(enabler).mapValues(Left(_))
        val (substMap, inst) = Template.substitution(encoder, QuantificationManager.this,
          condVars, exprVars, condTree, Seq.empty, lambdas, baseSubst, pathVar._1, enabler)
        instantiation ++= inst

        val msubst = substMap.collect { case (c, Right(m)) => c -> m }
        val substituter = encoder.substitute(substMap.mapValues(_.encoded))
        instantiation ++= Template.instantiate(encoder, QuantificationManager.this,
          clauses, blockers, applications, Seq.empty, Map.empty, lambdas, substMap)

        for ((b,ms) <- allMatchers; m <- ms) {
          val sb = enablers ++ (if (b == start) Set.empty else Set(substituter(b)))
          val sm = m.substitute(substituter, msubst)

          if (strict && (matchers(m) || transMatchers(m))) {
            instantiation ++= instCtx.instantiate(sb, sm)(quantifications.toSeq : _*)
          } else if (!matchers(m)) {
            ignoredMatchers += ((currentGen + 3, sb, sm))
          }
        }

        instantiation
      }
    }

    def ignoreSubst(enablers: Set[T], subst: Map[T, Arg[T]]): Unit = {
      val msubst = subst.collect { case (c, Right(m)) => c -> m }
      val substituter = encoder.substitute(subst.mapValues(_.encoded))
      val nextGen = (if (matchers.forall { m =>
        val sm = m.substitute(substituter, msubst)
        instCtx(enablers -> sm)
      }) currentGen + 3 else currentGen + 3)

      ignoredSubsts(this) += ((nextGen, enablers, subst))
    }

    protected def instanceSubst(enabler: T): Map[T, T]

    protected def skip(subst: Map[T, Arg[T]]): Boolean = false
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

  private lazy val blockerId = FreshIdentifier("blocker", BooleanType, true)
  private lazy val enablersToBlocker: MutableMap[Set[T], T] = MutableMap.empty
  private lazy val blockerToEnablers: MutableMap[T, Set[T]] = MutableMap.empty
  private def freshBlocker(enablers: Set[T]): (T, Option[T]) = enablers.toSeq match {
    case Seq(b) if isBlocker(b) => (b, None)
    case _ =>
      val last = enablersToBlocker.get(enablers).orElse {
        val initialEnablers = enablers.flatMap(blockerToEnablers.get).flatten
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
    val lambdas: Seq[LambdaTemplate[T]]) extends MatcherQuantification {

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

    val quantifiers = quantified zip uniformQuants(quantified)
    val key = template.key -> quantifiers

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

      val enablingClause = encoder.mkImplies(guardT, blockerT)

      instantiateAxiom(
        template.pathVar._1 -> substituter(template.start),
        blockerT,
        guardT,
        quantifiers,
        qMatchers,
        allMatchers + (template.start -> (allMatchers.getOrElse(template.start, Set.empty) + selfMatcher)),
        template.condVars map { case (id, idT) => id -> substituter(idT) },
        template.exprVars map { case (id, idT) => id -> substituter(idT) },
        template.condTree,
        (template.clauses map substituter) :+ enablingClause,
        template.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(
            args = fi.args.map(_.substitute(substituter, msubst))
          ))
        },
        template.applications map { case (b, apps) =>
          substituter(b) -> apps.map(app => app.copy(
            caller = substituter(app.caller),
            args = app.args.map(_.substitute(substituter, msubst))
          ))
        },
        template.lambdas map (_.substitute(substituter, msubst))
      )
    }
  }

  def instantiateAxiom(
    pathVar: (Identifier, T),
    blocker: T,
    guardVar: T,
    quantifiers: Seq[(Identifier, T)],
    matchers: Set[Matcher[T]],
    allMatchers: Map[T, Set[Matcher[T]]],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    condTree: Map[Identifier, Set[Identifier]],
    clauses: Seq[T],
    blockers: Map[T, Set[TemplateCallInfo[T]]],
    applications: Map[T, Set[App[T]]],
    lambdas: Seq[LambdaTemplate[T]]
  ): Instantiation[T] = {
    val quantified = quantifiers.map(_._2).toSet
    val matchQuorums = extractQuorums(quantified, matchers, lambdas)

    var instantiation = Instantiation.empty[T]

    for (matchers <- matchQuorums) {
      val axiom = new LambdaAxiom(pathVar, blocker, guardVar, quantifiers,
        matchers, allMatchers, condVars, exprVars, condTree,
        clauses, blockers, applications, lambdas
      )

      quantifications += axiom
      handledSubsts += axiom -> MutableSet.empty
      ignoredSubsts += axiom -> MutableSet.empty

      val newCtx = new InstantiationContext()
      for ((b,m) <- instCtx.instantiated) {
        instantiation ++= newCtx.instantiate(b, m)(axiom)
      }
      instCtx.merge(newCtx)
    }

    val quantifierSubst = uniformSubst(quantifiers)
    val substituter = encoder.substitute(quantifierSubst)

    for {
      m <- matchers
      sm = m.substitute(substituter, Map.empty)
      if !instCtx.corresponding(sm).exists(_._2.args == sm.args)
    } instantiation ++= instCtx.instantiate(Set.empty, sm)(quantifications.toSeq : _*)

    instantiation
  }

  def instantiateQuantification(template: QuantificationTemplate[T]): (T, Instantiation[T]) = {
    templates.get(template.key) match {
      case Some(idT) =>
        (idT, Instantiation.empty)

      case None =>
        val qT = encoder.encodeId(template.qs._1)
        val quantified = template.quantifiers.map(_._2).toSet
        val matchQuorums = extractQuorums(quantified, template.matchers.flatMap(_._2).toSet, template.lambdas)

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
            template.blockers, template.applications, template.lambdas
          )

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

        val quantifierSubst = uniformSubst(template.quantifiers)
        val substituter = encoder.substitute(quantifierSubst)

        for {
          (_, ms) <- template.matchers; m <- ms
          sm = m.substitute(substituter, Map.empty)
          if !instCtx.corresponding(sm).exists(_._2.args == sm.args)
        } instantiation ++= instCtx.instantiate(Set.empty, sm)(quantifications.toSeq : _*)

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
      instCtx.instantiate(bs, m)(quantifications.toSeq : _*)
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

  def checkClauses: Seq[T] = {
    val clauses = new scala.collection.mutable.ListBuffer[T]
    //val keySets = scala.collection.mutable.Map.empty[MatcherKey, T]
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

        val disjuncts = insts.toSeq.map { case (b, m) =>
          val subst = (elemsP.map(_._2) zip m.args.map(_.encoded)).toMap + (guardP._2 -> b)
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

    for ((key, ctx) <- instCtx.map.instantiations) {
      val QTM(argTypes, _) = key.tpe

      for {
        (tpe,idx) <- argTypes.zipWithIndex
        quants <- uniformQuantMap.get(tpe) if quants.nonEmpty
        (b, m) <- ctx
        arg = m.args(idx).encoded if !isQuantifier(arg)
      } clauses += encoder.mkAnd(quants.map(q => encoder.mkNot(encoder.mkEquals(q, arg))) : _*)
    }

    clauses.toSeq
  }
}
