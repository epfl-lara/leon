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

          if (matchers.map(_._1).toSet.size != 1)
            ctx.reporter.warning("Quantification conjuncts must contain exactly one matcher in " + conjunct)

          preTraversal {
            case Matcher(_, _) => // OK
            case LessThan(_: Variable, _: Variable) => // OK
            case LessEquals(_: Variable, _: Variable) => // OK
            case GreaterThan(_: Variable, _: Variable) => // OK
            case GreaterEquals(_: Variable, _: Variable) => // OK
            case And(_) => // OK
            case Or(_) => // OK
            case Implies(_, _) => // OK
            case BinaryOperator(Matcher(_, _), _, _) => // OK
            case BinaryOperator(_, Matcher(_, _), _) => // OK
            case BinaryOperator(e1, _, _) if (variablesOf(e1) & quantified).isEmpty => // OK
            case BinaryOperator(_, e2, _) if (variablesOf(e2) & quantified).isEmpty => // OK
            case FunctionInvocation(_, args) if {
              val argVars = args.flatMap(variablesOf).toSet
              (argVars & quantified).size <= 1 && (argVars & free).isEmpty
            } => // OK
            case UnaryOperator(_, _) => // OK
            case BinaryOperator(e1, e2, _) if ((variablesOf(e1) ++ variablesOf(e2)) & quantified).isEmpty => // OK
            case NAryOperator(es, _) if (es.flatMap(variablesOf).toSet & quantified).isEmpty => // OK
            case _: Terminal => // OK
            case e => ctx.reporter.warning("Invalid operation " + e + " on quantified variables")
          } (conjunct)
        }
      }
    }
  }
}
