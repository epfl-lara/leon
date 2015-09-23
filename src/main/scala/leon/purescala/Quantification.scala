/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._
import Types._

object Quantification {

  def extractQuorums[A,B](
    matchers: Set[A],
    quantified: Set[B],
    margs: A => Set[A],
    qargs: A => Set[B]
  ): Seq[Set[A]] = {
    def rec(oms: Seq[A], mSet: Set[A], qss: Seq[Set[B]]): Seq[Set[A]] = {
      if (qss.exists(_ == quantified)) {
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

    def expand(m: A): Set[A] = Set(m) ++ margs(m).flatMap(expand)
    val oms = matchers.toSeq.sortBy(m => -expand(m).size)
    rec(oms, Set.empty, Seq.empty)
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

  object HenkinDomains {
    def empty = new HenkinDomains(Map.empty)
    def apply(domains: Map[TypeTree, Set[Seq[Expr]]]) = new HenkinDomains(domains)
  }

  class HenkinDomains (val domains: Map[TypeTree, Set[Seq[Expr]]]) {
    def get(e: Expr): Set[Seq[Expr]] = e match {
      case PartialLambda(mapping, _) => mapping.map(_._1).toSet
      case _ => domains.get(e.getType) match {
        case Some(domain) => domain
        case None => scala.sys.error("Undefined Henkin domain for " + e)
      }
    }
  }

  object QuantificationMatcher {
    def unapply(expr: Expr): Option[(Expr, Seq[Expr])] = expr match {
      case Application(_: Application | _: FunctionInvocation, _) => None
      case Application(e, args) => Some(e -> args)
      case ArraySelect(arr, index) => Some(arr -> Seq(index))
      case MapApply(map, key) => Some(map -> Seq(key))
      case ElementOfSet(elem, set) => Some(set -> Seq(elem))
      case _ => None
    }
  }

  object QuantificationTypeMatcher {
    def unapply(tpe: TypeTree): Option[(Seq[TypeTree], TypeTree)] = tpe match {
      case FunctionType(from, to) => Some(from -> to)
      case ArrayType(base) => Some(Seq(Int32Type) -> base)
      case MapType(from, to) => Some(Seq(from) -> to)
      case SetType(base) => Some(Seq(base) -> BooleanType)
      case _ => None
    }
  }

  object CheckForalls extends UnitPhase[Program] {
    
    val name = "Foralls"
    val description = "Check syntax of foralls to guarantee sound instantiations"

    def apply(ctx: LeonContext, program: Program) = {
      program.definedFunctions.foreach { fd =>
        val foralls = collect[Forall] {
          case f: Forall => Set(f)
          case _ => Set.empty
        } (fd.fullBody)

        val free = fd.params.map(_.id).toSet ++ (fd.postcondition match {
          case Some(Lambda(args, _)) => args.map(_.id)
          case _ => Seq.empty
        })

        for (Forall(args, TopLevelAnds(conjuncts)) <- foralls) {
          val quantified = args.map(_.id).toSet

          for (conjunct <- conjuncts) {
            val matchers = collect[(Expr, Seq[Expr])] {
              case QuantificationMatcher(e, args) => Set(e -> args)
              case _ => Set.empty
            } (conjunct)

            if (matchers.isEmpty)
              ctx.reporter.warning("E-matching isn't possible without matchers!")

            if (matchers.exists { case (_, args) =>
              args.exists(arg => arg match {
                case QuantificationMatcher(_, _) => false
                case Variable(id) => false
                case _ if (variablesOf(arg) & quantified).nonEmpty => true
                case _ => false
              })
            }) ctx.reporter.warning("Matcher arguments must have simple form in " + conjunct)

            val freeMatchers = matchers.collect { case (Variable(id), args) if free(id) => id -> args }

            val id2Quant = freeMatchers.foldLeft(Map.empty[Identifier, Set[Identifier]]) {
              case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
                case Variable(id) if quantified(id) => Set(id)
                case _ => Set.empty[Identifier]
              }))
            }

            if (id2Quant.filter(_._2.nonEmpty).groupBy(_._2).size >= 1)
              ctx.reporter.warning("Multiple matchers must provide bijective matching in " + conjunct)

            foldRight[Set[Identifier]] { case (m, children) =>
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
                  val vars = es.flatMap {
                    case Variable(id) => Set(id)
                    case _ => Set.empty[Identifier]
                  }.toSet

                  if (!(q.isEmpty || (q.size == 1 && (vars & free).isEmpty)))
                    ctx.reporter.warning("Invalid operation " + m + " on quantified variables")
                  q -- vars
                case Variable(id) if quantified(id) => Set(id)
                case _ => q
              }
            } (conjunct)
          }
        }
      }
    }
  }
}
