/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._

object CheckForalls extends UnitPhase[Program] {
  
  val name = "Foralls"
  val description = "Check syntax of foralls to guarantee sound instantiations"

  def apply(ctx: LeonContext, program: Program) = {
    program.definedFunctions.foreach { fd =>
      if (fd.body.exists(b => exists {
        case f: Forall => true
        case _ => false
      } (b))) ctx.reporter.warning("Universal quantification in function bodies is not supported in " + fd)

      val foralls = (fd.precondition.toSeq ++ fd.postcondition.toSeq).flatMap { prec =>
        collect[Forall] {
          case f: Forall => Set(f)
          case _ => Set.empty
        } (prec)
      }

      val free = fd.params.map(_.id).toSet ++ (fd.postcondition match {
        case Some(Lambda(args, _)) => args.map(_.id)
        case _ => Seq.empty
      })

      object Matcher {
        def unapply(e: Expr): Option[(Identifier, Seq[Expr])] = e match {
          case Application(Variable(id), args) if free(id) => Some(id -> args)
          case ArraySelect(Variable(id), index) if free(id) => Some(id -> Seq(index))
          case MapGet(Variable(id), key) if free(id) => Some(id -> Seq(key))
          case _ => None
        }
      }

      for (Forall(args, TopLevelAnds(conjuncts)) <- foralls) {
        val quantified = args.map(_.id).toSet

        for (conjunct <- conjuncts) {
          val matchers = collect[(Identifier, Seq[Expr])] {
            case Matcher(id, args) => Set(id -> args)
            case _ => Set.empty
          } (conjunct)

          if (matchers.exists { case (id, args) =>
            args.exists(arg => arg match {
              case Matcher(_, _) => false
              case Variable(id) => false
              case _ if (variablesOf(arg) & quantified).nonEmpty => true
              case _ => false
            })
          }) ctx.reporter.warning("Matcher arguments must have simple form in " + conjunct)

          val id2Quant = matchers.foldLeft(Map.empty[Identifier, Set[Identifier]]) {
            case (acc, (m, args)) => acc + (m -> (acc.getOrElse(m, Set.empty) ++ args.flatMap {
              case Variable(id) if quantified(id) => Set(id)
              case _ => Set.empty[Identifier]
            }))
          }

          if (id2Quant.filter(_._2.nonEmpty).groupBy(_._2).size != 1)
            ctx.reporter.warning("Multiple matchers must provide bijective matching in " + conjunct)

          foldRight[Set[Identifier]] { case (m, children) =>
            val q = children.toSet.flatten

            m match {
              case Matcher(_, args) =>
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
