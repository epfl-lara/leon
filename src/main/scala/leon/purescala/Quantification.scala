/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
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
    val expandedMap: Map[A, Set[A]] = matchers.map(m => m -> expand(m)).toMap
    val reverseMap : Map[A, Set[A]] = expandedMap
      .flatMap(p => p._2.map(m => m -> p._1))     // flatten to reversed pairs
      .groupBy(_._1).mapValues(_.map(_._2).toSet) // rebuild map from pair set

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

  def extractQuorums(expr: Expr, quantified: Set[Identifier]): Seq[Set[(Expr, Seq[Expr])]] = {
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

    extractQuorums(collect {
      case QMatcher(e, a) => Set(e -> a)
      case _ => Set.empty[(Expr, Seq[Expr])]
    } (expr), quantified,
    (p: (Expr, Seq[Expr])) => p._2.collect { case QMatcher(e, a) => e -> a }.toSet,
    (p: (Expr, Seq[Expr])) => p._2.collect { case Variable(id) if quantified(id) => id }.toSet)
  }

  def extractModel(
    asMap: Map[Identifier, Expr],
    funDomains: Map[Identifier, Set[Seq[Expr]]],
    tpeDomains: Map[TypeTree, Set[Seq[Expr]]],
    evaluator: Evaluator
  ): Map[Identifier, Expr] = asMap.map { case (id, expr) =>
    id -> (funDomains.get(id) match {
      case Some(domain) =>
        PartialLambda(domain.toSeq.map { es =>
          val optEv = evaluator.eval(Application(expr, es)).result
          es -> optEv.getOrElse(scala.sys.error("Unexpectedly failed to evaluate " + Application(expr, es)))
        }, None, id.getType.asInstanceOf[FunctionType])

      case None => postMap {
        case p @ PartialLambda(mapping, dflt, tpe) =>
          Some(PartialLambda(tpeDomains.get(tpe) match {
            case Some(domain) => domain.toSeq.map { es =>
              val optEv = evaluator.eval(Application(p, es)).result
              es -> optEv.getOrElse(scala.sys.error("Unexpectedly failed to evaluate " + Application(p, es)))
            }
            case _ => scala.sys.error(s"Can't extract $p without domain")
          }, None, tpe))
        case _ => None
      } (expr)
    })
  }

  object HenkinDomains {
    def empty = new HenkinDomains(Map.empty)
    def apply(domains: Map[TypeTree, Set[Seq[Expr]]]) = new HenkinDomains(domains)
  }

  class HenkinDomains (val domains: Map[TypeTree, Set[Seq[Expr]]]) {
    def get(e: Expr): Set[Seq[Expr]] = e match {
      case PartialLambda(_, Some(dflt), _) => scala.sys.error("No domain for non-partial lambdas")
      case PartialLambda(mapping, _, _) => mapping.map(_._1).toSet
      case _ => domains.get(e.getType) match {
        case Some(domain) => domain
        case None => scala.sys.error("Undefined Henkin domain for " + e)
      }
    }

    override def toString = domains.map { case (tpe, argSet) =>
      tpe + ": " + argSet.map(_.mkString("(", ",", ")")).mkString(", ")
    }.mkString("domain={\n  ", "\n  ", "}")
  }

  object QuantificationMatcher {
    private def flatApplication(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(fi: FunctionInvocation, _) => None
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

  sealed abstract class ForallInvalid extends ForallStatus {
    def isValid = false
  }

  case object NoMatchers extends ForallInvalid
  case class ComplexArgument(expr: Expr) extends ForallInvalid
  case class NonBijectiveMapping(expr: Expr) extends ForallInvalid
  case class InvalidOperation(expr: Expr) extends ForallInvalid

  def checkForall(quantified: Set[Identifier], body: Expr): ForallStatus = {
    val TopLevelAnds(conjuncts) = body
    for (conjunct <- conjuncts) {
      val matchers = collect[(Expr, Seq[Expr])] {
        case QuantificationMatcher(e, args) => Set(e -> args)
        case _ => Set.empty
      } (conjunct)

      if (matchers.isEmpty) return NoMatchers

      val complexArgs = matchers.flatMap { case (_, args) =>
        args.flatMap(arg => arg match {
          case QuantificationMatcher(_, _) => None
          case Variable(id) => None
          case _ if (variablesOf(arg) & quantified).nonEmpty => Some(arg)
          case _ => None
        })
      }

      if (complexArgs.nonEmpty) return ComplexArgument(complexArgs.head)

      val matcherToQuants = matchers.foldLeft(Map.empty[Expr, Set[Identifier]]) {
        case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
          case Variable(id) if quantified(id) => Set(id)
          case _ => Set.empty[Identifier]
        }))
      }

      val bijectiveMappings = matcherToQuants.filter(_._2.nonEmpty).groupBy(_._2)
      if (bijectiveMappings.size > 1) return NonBijectiveMapping(bijectiveMappings.head._2.head._1)

      val matcherSet = matcherToQuants.filter(_._2.nonEmpty).keys.toSet

      val qs = foldRight[Set[Identifier]] { case (m, children) =>
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
              return InvalidOperation(m)
            else Set.empty
          case Variable(id) if quantified(id) => Set(id)
          case _ => q
        }
      } (conjunct)
    }

    ForallValid
  }
}
