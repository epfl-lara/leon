/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Constructors._
import Extractors._
import ExprOps._
import Types._

import evaluators._

object Quantification {

  def extractQuorums[A,B](
    matchers: Set[A],
    quantified: Set[B],
    margs: A => Set[A],
    qargs: A => Set[B]
  ): Seq[Set[A]] = {
    def expand(m: A): Set[A] = Set(m) ++ margs(m).flatMap(expand)
    def allQArgs(m: A): Set[B] = qargs(m) ++ margs(m).flatMap(allQArgs)
    val expandedMap: Map[A, Set[A]] = matchers.map(m => m -> expand(m)).toMap
    val reverseMap : Map[A, Set[A]] = expandedMap.toSeq
      .flatMap(p => p._2.map(m => m -> p._1))     // flatten to reversed pairs
      .groupBy(_._1).mapValues(_.map(_._2).toSet) // rebuild map from pair set
      .map { case (m, ms) =>                      // filter redundant matchers
        val allM = allQArgs(m)
        m -> ms.filter(rm => allQArgs(rm) != allM)
      }

    def rec(oms: Seq[A], mSet: Set[A], qss: Seq[Set[B]]): Seq[Set[A]] = {
      if (qss.contains(quantified)) {
        Seq(mSet)
      } else {
        var res = Seq.empty[Set[A]]
        val rest = oms.scanLeft(List.empty[A])((acc, o) => o :: acc).drop(1)
        for ((m :: ms) <- rest if margs(m).forall(mSet)) {
          val qas = qargs(m)
          if (!qss.exists(qs => qs.subsetOf(qas) || qas.subsetOf(qs))) {
            res ++= rec(ms, mSet + m, qss ++ qss.map(_ ++ qas) :+ qas)
          }
        }
        res
      }
    }

    val oms = expandedMap.toSeq.sortBy(p => -p._2.size).map(_._1)
    val res = rec(oms, Set.empty, Seq.empty)

    res.filter(ms => ms.forall(m => reverseMap(m) subsetOf ms))
  }

  def extractQuorums(expr: Expr, quantified: Set[Identifier]): Seq[Set[(Path, Expr, Seq[Expr])]] = {
    object QMatcher {
      def unapply(e: Expr): Option[(Expr, Seq[Expr])] = e match {
        case QuantificationMatcher(expr, args) =>
          if (args.exists { case Variable(id) => quantified(id) case _ => false }) {
            Some(expr -> args)
          } else {
            None
          }
        case _ => None
      }
    }

    val allMatchers = CollectorWithPaths { case QMatcher(expr, args) => expr -> args }.traverse(expr)
    val matchers = allMatchers.map { case ((caller, args), path) => (path, caller, args) }.toSet

    extractQuorums(matchers, quantified,
      (p: (Path, Expr, Seq[Expr])) => p._3.collect { case QMatcher(e, a) => (p._1, e, a) }.toSet,
      (p: (Path, Expr, Seq[Expr])) => p._3.collect { case Variable(id) if quantified(id) => id }.toSet)
  }

  object Domains {
    def empty = new Domains(Map.empty, Map.empty)
  }

  class Domains (_lambdas: Map[Lambda, Set[Seq[Expr]]], val tpes: Map[TypeTree, Set[Seq[Expr]]]) {
    val lambdas = _lambdas.map { case (lambda, domain) =>
      val (nl, _) = normalizeStructure(lambda)
      nl -> domain
    }

    def get(e: Expr): Set[Seq[Expr]] = {
      val specialized: Set[Seq[Expr]] = e match {
        case FiniteLambda(mapping, _, _) => mapping.map(_._1).toSet
        case l: Lambda =>
          val (nl, _) = normalizeStructure(l)
          lambdas.getOrElse(nl, Set.empty)
        case _ => Set.empty
      }
      specialized ++ tpes.getOrElse(e.getType, Set.empty)
    }
  }

  object QuantificationMatcher {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, args) => None
      case Application(caller: Application, args) => flatApplication(caller) match {
        case Some((c, prevArgs)) => Some((c, prevArgs ++ args))
        case None => None
      }
      case Application(caller, args) => Some((caller, args))
      case _ => None
    }

    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case IsTyped(a: Application, ft: FunctionType) => None
      case Application(e, args) => flatApplication(expr)
      case ArraySelect(arr, index) => Some(arr -> Seq(index))
      case MapApply(map, key) => Some(map -> Seq(key))
      case ElementOfSet(elem, set) => Some(set -> Seq(elem))
      case _ => None
    }
  }

  object QuantificationTypeMatcher {
    private def flatType(tpe: TypeTree): (Seq[TypeTree], TypeTree) = tpe match {
      case FunctionType(from, to) =>
        val (nextArgs, finalTo) = flatType(to)
        (from ++ nextArgs, finalTo)
      case _ => (Seq.empty, tpe)
    }

    def unapply(tpe: TypeTree): Option[(Seq[TypeTree], TypeTree)] = tpe match {
      case FunctionType(from, to) => Some(flatType(tpe))
      case ArrayType(base) => Some(Seq(Int32Type) -> base)
      case MapType(from, to) => Some(Seq(from) -> to)
      case SetType(base) => Some(Seq(base) -> BooleanType)
      case _ => None
    }
  }

  sealed abstract class ForallStatus {
    def isValid: Boolean
  }

  case object ForallValid extends ForallStatus {
    def isValid = true
  }

  sealed abstract class ForallInvalid(msg: String) extends ForallStatus {
    def isValid = false
    def getMessage: String = msg
  }

  case class NoMatchers(expr: String) extends ForallInvalid("No matchers available for E-Matching in " + expr)
  case class ComplexArgument(expr: String) extends ForallInvalid("Unhandled E-Matching pattern in " + expr)
  case class NonBijectiveMapping(expr: String) extends ForallInvalid("Non-bijective mapping for quantifiers in " + expr)
  case class InvalidOperation(expr: String) extends ForallInvalid("Invalid operation on quantifiers in " + expr)

  def checkForall(quantified: Set[Identifier], body: Expr)(implicit ctx: LeonContext): ForallStatus = {
    val TopLevelAnds(conjuncts) = body
    for (conjunct <- conjuncts) {
      val matchers = collect[(Expr, Seq[Expr])] {
        case QuantificationMatcher(e, args) => Set(e -> args)
        case _ => Set.empty
      } (conjunct)

      if (matchers.isEmpty) return NoMatchers(conjunct.asString)

      val complexArgs = matchers.flatMap { case (_, args) =>
        args.flatMap(arg => arg match {
          case QuantificationMatcher(_, _) => None
          case Variable(id) => None
          case _ if (variablesOf(arg) & quantified).nonEmpty => Some(arg)
          case _ => None
        })
      }

      if (complexArgs.nonEmpty) return ComplexArgument(complexArgs.head.asString)

      val matcherToQuants = matchers.foldLeft(Map.empty[Expr, Set[Identifier]]) {
        case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
          case Variable(id) if quantified(id) => Set(id)
          case _ => Set.empty[Identifier]
        }))
      }

      val bijectiveMappings = matcherToQuants.filter(_._2.nonEmpty).groupBy(_._2)
      if (bijectiveMappings.size > 1) return NonBijectiveMapping(bijectiveMappings.head._2.head._1.asString)

      val matcherSet = matcherToQuants.filter(_._2.nonEmpty).keys.toSet

      val qs = fold[Set[Identifier]] { case (m, children) =>
        val q = children.toSet.flatten

        m match {
          case QuantificationMatcher(_, args) =>
            q -- args.flatMap {
              case Variable(id) if quantified(id) => Set(id)
              case _ => Set.empty[Identifier]
            }
          case LessThan(_: Variable, _: Variable) => q
          case LessEquals(_: Variable, _: Variable) => q
          case GreaterThan(_: Variable, _: Variable) => q
          case GreaterEquals(_: Variable, _: Variable) => q
          case And(_) => q
          case Or(_) => q
          case Implies(_, _) => q
          case Operator(es, _) =>
            val matcherArgs = matcherSet & es.toSet
            if (q.nonEmpty && !(q.size == 1 && matcherArgs.isEmpty && m.getType == BooleanType))
              return InvalidOperation(m.asString)
            else Set.empty
          case Variable(id) if quantified(id) => Set(id)
          case _ => q
        }
      } (conjunct)
    }

    ForallValid
  }
}
