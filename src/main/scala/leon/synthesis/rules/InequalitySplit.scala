/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.synthesis.Witnesses.Inactive
import purescala.Expressions._
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._

/** For every pair of variables of an integer type plus 0 of that type,
  * splits for inequality between these variables
  * and reconstructs the subproblems with a (nested) if-then-else.
  *
  * Takes into account knowledge about equality/inequality in the path condition.
  *
  */
case object InequalitySplit extends Rule("Ineq. Split.") {

  // Represents NEGATIVE knowledge
  private abstract class Fact {
    val l: Expr
    val r: Expr
  }
  private case class LT(l: Expr, r: Expr) extends Fact
  private case class EQ(l: Expr, r: Expr) extends Fact

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    def getFacts(e: Expr): Set[Fact] = e match {
      case LessThan(a, b)           => Set(LT(b,a), EQ(a,b))
      case LessEquals(a, b)         => Set(LT(b,a))
      case GreaterThan(a, b)        => Set(LT(a,b), EQ(a,b))
      case GreaterEquals(a, b)      => Set(LT(a,b))
      case Equals(a, b)             => Set(LT(a,b), LT(b,a))
      case Not(LessThan(a, b))      => Set(LT(a,b))
      case Not(LessEquals(a, b))    => Set(LT(a,b), EQ(a,b))
      case Not(GreaterThan(a, b))   => Set(LT(b,a))
      case Not(GreaterEquals(a, b)) => Set(LT(b,a), EQ(a,b))
      case Not(Equals(a, b))        => Set(EQ(a,b))
      case _ => Set()
    }

    val facts: Set[Fact] = {
      val TopLevelAnds(fromPhi) = p.phi
      (fromPhi.toSet ++ p.pc.conditions ++ p.pc.bindings.map { case (id,e) => Equals(id.toVariable, e) }) flatMap getFacts
    }

    val candidates =
      (p.allAs.map(_.toVariable).filter(_.getType == Int32Type) :+ IntLiteral(0)).combinations(2).toList ++
      (p.allAs.map(_.toVariable).filter(_.getType == IntegerType) :+ InfiniteIntegerLiteral(0)).combinations(2).toList

    candidates.flatMap {
      case List(v1, v2) =>

        val lt = if (!facts.contains(LT(v1, v2))) {
          val pc = LessThan(v1, v2)
          Some(pc, p.copy(pc = p.pc withCond pc))
        } else None

        val gt = if (!facts.contains(LT(v2, v1))) {
          val pc = GreaterThan(v1, v2)
          Some(pc, p.copy(pc = p.pc withCond pc))
        } else None

        val eq = if (!facts.contains(EQ(v1, v2)) && !facts.contains(EQ(v2,v1))) {
          val pc = Equals(v1, v2)
          // Let's see if an input variable is involved
          val (f, t, isInput) = (v1, v2) match {
            case (Variable(a1), _) if p.as.contains(a1) => (a1, v2, true)
            case (_, Variable(a2)) if p.as.contains(a2) => (a2, v1, true)
            case (Variable(a1), _)                      => (a1, v2, false)
          }
          val newP = if (isInput) {
            p.copy(
              as = p.as.diff(Seq(f)),
              pc = p.pc map (subst(f -> t, _)),
              ws = subst(f -> t, p.ws),
              phi = subst(f -> t, p.phi),
              eb = p.qeb.removeIns(Set(f))
            )
          } else {
            p.copy(pc = p.pc withCond pc).withWs(Seq(Inactive(f))) // equality in pc is fine for numeric types
          }

          Some(pc, newP)
        } else None

        val (pcs, subProblems) = List(eq, lt, gt).flatten.unzip

        if (pcs.size < 2) None
        else {

          val onSuccess: List[Solution] => Option[Solution] = { sols =>
            val pre = orJoin(pcs.zip(sols).map { case (pc, sol) => and(pc, sol.pre) })

            val term = pcs.zip(sols) match {
              case Seq((pc1, s1), (_, s2)) =>
                IfExpr(pc1, s1.term, s2.term)
              case Seq((pc1, s1), (pc2, s2), (_, s3)) =>
                IfExpr(pc1, s1.term, IfExpr(pc2, s2.term, s3.term))
            }

            Some(Solution(pre, sols.flatMap(_.defs).toSet, term, sols.forall(_.isTrusted)))
          }

          Some(decomp(subProblems, onSuccess, s"Ineq. Split on '$v1' and '$v2'"))
        }
    }
  }
}
