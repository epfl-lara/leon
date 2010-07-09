package orderedsets

import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model

class UnifierMain(reporter: Reporter) extends Solver(reporter) {
  import purescala.Trees.{Expr, And, Not, Equals, negate, expandLets}
  import DNF._

  val description = "Unifier testbench"
  override val shortDescription = "Unifier"

  // checks for V-A-L-I-D-I-T-Y !
  // Some(true) means formula is valid (negation is unsat)
  // Some(false) means formula is not valid (negation is sat)
  // None means you don't know.
  //
  def solve(exprWithLets: Expr): Option[Boolean] = {
    val expr = expandLets(exprWithLets)
    try {
      reporter.info("")
      expr match {
        case and @ And(_) =>
          PureScalaUnifier.unify(and)
          Some(true)
        case Equals(_, _) | Not(Equals(_, _)) =>
          PureScalaUnifier.unify(expr)
          Some(true)
          //None
        case _ => throw ConversionException(expr, "Neither a conjunction nor a (in)equality")
      }
      
    } catch {
      case PureScalaUnifier.UnificationFailure(msg) =>
        reporter.info("Unification impossible : " + msg)
        Some(false)
      case ConversionException(badExpr, msg) =>
        reporter.info(msg + " : " + badExpr.getClass.toString)
//        reporter.info(DNF.pp(badExpr))
        None
      case e =>
        reporter.error("Unifier just crashed.\n  exception = " + e.toString)
        e.printStackTrace
        None
    } finally {
      
    }
  }

}
