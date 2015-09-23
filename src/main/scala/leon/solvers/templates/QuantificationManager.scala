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
    q2: Identifier,
    inst: Identifier,
    guard: Identifier,
    quantifiers: Seq[(Identifier, T)],
    condVars: Map[Identifier, T],
    exprVars: Map[Identifier, T],
    guardedExprs: Map[Identifier, Seq[Expr]],
    lambdas: Map[T, LambdaTemplate[T]],
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
  private lazy val trueT = encoder.encodeExpr(Map.empty)(BooleanLiteral(true))

  private val quantifications = new IncrementalSeq[Quantification]
  private val instantiated    = new IncrementalSet[(T, Matcher[T])]
  private val fInsts          = new IncrementalSet[Matcher[T]]
  private val known           = new IncrementalSet[T]

  private def fInstantiated = fInsts.map(m => trueT -> m)

  private def correspond(qm: Matcher[T], m: Matcher[T]): Boolean = correspond(qm, m.caller, m.tpe)
  private def correspond(qm: Matcher[T], caller: T, tpe: TypeTree): Boolean = qm.tpe match {
    case _: FunctionType => qm.tpe == tpe && (qm.caller == caller || !known(caller))
    case _ => qm.tpe == tpe
  }

  private val uniformQuantifiers = scala.collection.mutable.Map.empty[TypeTree, Seq[T]]
  private def uniformSubst(qs: Seq[(Identifier, T)]): Map[T, T] = {
    qs.groupBy(_._1.getType).flatMap { case (tpe, qst) =>
      val prev = uniformQuantifiers.get(tpe) match {
        case Some(seq) => seq
        case None => Seq.empty
      }

      if (prev.size >= qst.size) {
        qst.map(_._2) zip prev.take(qst.size - 1)
      } else {
        val (handled, newQs) = qst.splitAt(prev.size)
        val uQs = newQs.map(p => p._2 -> encoder.encodeId(p._1))
        uniformQuantifiers(tpe) = prev ++ uQs.map(_._2)
        (handled.map(_._2) zip prev) ++ uQs
      }
    }.toMap
  }

  override protected def incrementals: List[IncrementalState] =
    List(quantifications, instantiated, fInsts, known) ++ super.incrementals

  def assumptions: Seq[T] = quantifications.map(_.currentQ2Var).toSeq

  def instantiations: Seq[(T, Matcher[T])] = instantiated.toSeq ++ fInstantiated

  def instantiations(caller: T, tpe: TypeTree): Seq[(T, Matcher[T])] =
    instantiations.filter { case (b,m) => correspond(m, caller, tpe) }

  override def registerFree(ids: Seq[(TypeTree, T)]): Unit = {
    super.registerFree(ids)
    known ++= ids.map(_._2)
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
    val lambdas: Map[T, LambdaTemplate[T]]) {

    var currentQ2Var: T = qs._2
    private var slaves: Seq[(T, Map[T,T], Quantification)] = Nil

    private def mappings(blocker: T, matcher: Matcher[T])
                        (implicit instantiated: Iterable[(T, Matcher[T])]): Set[(T, Map[T, T])] = {

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
              val instances: Set[(T, Matcher[T])] = instantiated.filter { case (b, m) => correspond(qm, m) }.toSet

              // concrete applications can appear multiple times in the constraint, and this is also the case
              // for the current application for which we are generating the constraints
              val withCurrent = if (correspond(qm, matcher)) instances + (blocker -> matcher) else instances

              qm -> withCurrent
            }).toMap

          // 2.2. based on the possible bindings for each quantified application, build a set of
          //      instantiation mappings that can be used to instantiate all necessary constraints
          extractMappings(matcherToInstances)
        }

      for (mapping <- matcherMappings) yield extractSubst(quantified, mapping)
    }

    private def extractSlaveInfo(enabler: T, senabler: T, subst: Map[T,T], ssubst: Map[T,T]): (T, Map[T,T]) = {
      val substituter = encoder.substitute(subst)
      val slaveEnabler = encoder.mkAnd(enabler, substituter(senabler))
      val slaveSubst = ssubst.map(p => p._1 -> substituter(p._2))
      (slaveEnabler, slaveSubst)
    }

    private def instantiate(enabler: T, subst: Map[T, T], seen: Set[Quantification]): Instantiation[T] = {
      if (seen(this)) {
        Instantiation.empty[T]
      } else {
        val nextQ2Var = encoder.encodeId(q2s._1)

        val baseSubstMap = (condVars ++ exprVars).map { case (id, idT) => idT -> encoder.encodeId(id) }
        val lambdaSubstMap = lambdas map { case (idT, lambda) => idT -> encoder.encodeId(lambda.id) }
        val substMap = subst ++ baseSubstMap ++ lambdaSubstMap +
          (qs._2 -> currentQ2Var) + (guardVar -> enabler) + (q2s._2 -> nextQ2Var) +
          (insts._2 -> encoder.encodeId(insts._1))

        var instantiation = Template.instantiate(encoder, QuantificationManager.this,
          clauses, blockers, applications, Seq.empty, Map.empty[T, Set[Matcher[T]]], lambdas, substMap)

        for {
          (senabler, ssubst, slave) <- slaves
          (slaveEnabler, slaveSubst) = extractSlaveInfo(enabler, senabler, subst, ssubst)
        } instantiation ++= slave.instantiate(slaveEnabler, slaveSubst, seen + this)

        currentQ2Var = nextQ2Var
        instantiation
      }
    }

    def register(senabler: T, ssubst: Map[T, T], slave: Quantification): Instantiation[T] = {
      var instantiation = Instantiation.empty[T]

      for {
        instantiated <- List(instantiated, fInstantiated)
        (blocker, matcher) <- instantiated
        (enabler, subst) <- mappings(blocker, matcher)(instantiated)
        (slaveEnabler, slaveSubst) = extractSlaveInfo(enabler, senabler, subst, ssubst)
      } instantiation ++= slave.instantiate(slaveEnabler, slaveSubst, Set(this))

      slaves :+= (senabler, ssubst, slave)

      instantiation
    }

    def instantiate(blocker: T, matcher: Matcher[T])(implicit instantiated: Iterable[(T, Matcher[T])]): Instantiation[T] = {
      var instantiation = Instantiation.empty[T]

      for ((enabler, subst) <- mappings(blocker, matcher)) {
        instantiation ++= instantiate(enabler, subst, Set.empty)
      }

      instantiation
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

  def instantiateQuantification(template: QuantificationTemplate[T], substMap: Map[T, T]): Instantiation[T] = {
    val quantified = template.quantifiers.map(_._2).toSet

    val allMatchers: Map[T, Set[Matcher[T]]] = {
      def rec(templates: Map[T, LambdaTemplate[T]]): Map[T, Set[Matcher[T]]] =
        templates.foldLeft(Map.empty[T, Set[Matcher[T]]]) {
          case (matchers, (_, template)) => matchers merge template.matchers merge rec(template.lambdas)
        }

      template.matchers merge rec(template.lambdas)
    }

    val quantifiedMatchers = (for {
      (_, ms) <- allMatchers
      m @ Matcher(_, _, args, _) <- ms
      if args exists (_.left.exists(quantified))
    } yield m).toSet

    val matchQuorums: Seq[Set[Matcher[T]]] = purescala.Quantification.extractQuorums(
      quantifiedMatchers, quantified,
      (m: Matcher[T]) => m.args.collect { case Right(m) if quantifiedMatchers(m) => m }.toSet,
      (m: Matcher[T]) => m.args.collect { case Left(a) if quantified(a) => a }.toSet)

    var instantiation = Instantiation.empty[T]

    val qs = for (matchers <- matchQuorums) yield {
      val newQ = encoder.encodeId(template.qs._1)
      val subst = substMap + (template.qs._2 -> newQ)

      val substituter = encoder.substitute(subst)
      val quantification = new Quantification(template.qs._1 -> newQ,
        template.q2s, template.insts, template.guardVar,
        quantified,
        matchers map (m => m.substitute(substituter)),
        allMatchers map { case (b, ms) => substituter(b) -> ms.map(_.substitute(substituter)) },
        template.condVars,
        template.exprVars,
        template.clauses map substituter,
        template.blockers map { case (b, fis) =>
          substituter(b) -> fis.map(fi => fi.copy(args = fi.args.map(substituter)))
        },
        template.applications map { case (b, fas) =>
          substituter(b) -> fas.map(fa => fa.copy(caller = substituter(fa.caller), args = fa.args.map(substituter)))
        },
        template.lambdas map { case (idT, template) => substituter(idT) -> template.substitute(subst) }
      )

      def extendClauses(master: Quantification, slave: Quantification): Instantiation[T] = {
        val bindingsMap: Map[Matcher[T], Set[(T, Matcher[T])]] = slave.matchers.map { sm =>
          val instances = master.allMatchers.toSeq.flatMap { case (b, ms) => ms.map(b -> _) }
          sm -> instances.filter(p => correspond(p._2, sm)).toSet
        }.toMap

        val allMappings = extractMappings(bindingsMap)
        val filteredMappings = allMappings.filter { s =>
          s.exists { case (b, sm, m) => !master.matchers(m) } &&
          s.exists { case (b, sm, m) => sm != m } &&
          s.forall { case (b, sm, m) =>
            (sm.args zip m.args).forall {
              case (Right(_), Left(_)) => false
              case _ => true
            }
          }
        }

        var instantiation = Instantiation.empty[T]

        for (mapping <- filteredMappings) {
          val (enabler, subst) = extractSubst(slave.quantified, mapping)
          instantiation ++= master.register(enabler, subst, slave)
        }

        instantiation
      }

      val allSet = quantification.allMatchers.flatMap(_._2).toSet
      for (q <- quantifications) {
        val allQSet = q.allMatchers.flatMap(_._2).toSet
        if (quantification.matchers.forall(m => allQSet.exists(qm => correspond(qm, m))))
          instantiation ++= extendClauses(q, quantification)

        if (q.matchers.forall(qm => allSet.exists(m => correspond(qm, m))))
          instantiation ++= extendClauses(quantification, q)
      }

      for (instantiated <- List(instantiated, fInstantiated); (b, m) <- instantiated) {
        instantiation ++= quantification.instantiate(b, m)(instantiated)
      }

      quantifications += quantification
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
      val sm = m.substitute(substituter)

      if (!fInsts.exists(fm => correspond(sm, fm) && sm.args == fm.args)) {
        for (q <- quantifications) {
          instantiation ++= q.instantiate(trueT, sm)(fInstantiated)
        }

        fInsts += sm
      }
    }

    instantiation
  }

  def instantiateMatcher(blocker: T, matcher: Matcher[T]): Instantiation[T] = {
    val qInst = if (instantiated(blocker -> matcher)) Instantiation.empty[T] else {
      var instantiation = Instantiation.empty[T]
      for (q <- quantifications) {
        instantiation ++= q.instantiate(blocker, matcher)(instantiated)
      }

      instantiated += (blocker -> matcher)

      instantiation
    }

    qInst
  }

}
