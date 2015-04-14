/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import scala.annotation.tailrec

import solvers._

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._

case object InlineHoles extends Rule("Inline-Holes") {
  override val priority = RulePriorityHoles

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // When true: withOracle gets converted into a big choose() on result.
    val sctx = hctx.sctx
    val discreteHoles = sctx.settings.distreteHoles

    if (!discreteHoles) {
      return Nil
    }

    val Some(oracleHead) = sctx.program.definedFunctions.find(_.id.name == "Oracle.head")

    def containsHoles(e: Expr): Boolean = {
      preTraversal{
        case FunctionInvocation(TypedFunDef(`oracleHead`, _), _) => return true
        case _ =>
      }(e)
      false
    }

    /**
     * Returns true if the expression directly or indirectly relies on a Hole
     */
    def usesHoles(e: Expr): Boolean = {
      var cache = Map[FunDef, Boolean]()

      def callsHolesExpr(e: Expr): Boolean = {
        containsHoles(e) || functionCallsOf(e).exists(fi => callsHoles(fi.tfd.fd))
      }

      def callsHoles(fd: FunDef): Boolean = cache.get(fd) match {
        case Some(r) => r
        case None =>
          cache += fd -> false

          val res = fd.body.exists(callsHolesExpr)

          cache += fd -> res
          res
      }

      callsHolesExpr(e)
    }

    @tailrec
    def inlineUntilHoles(e: Expr): Expr = {
      if (containsHoles(e)) {
        // Holes are exposed, no need to inline (yet)
        e
      } else {
        // Inline all functions "once" that contain holes
        val newE = postMap {
          case fi @ FunctionInvocation(tfd, args) if usesHoles(fi) && tfd.hasBody =>
            val inlined = replaceFromIDs((tfd.params.map(_.id) zip args).toMap, tfd.body.get)
            Some(inlined)

          case _ => None
        }(e)

        inlineUntilHoles(newE)
      }
    }

    def inlineHoles(phi: Expr): (List[Identifier], Expr) = {

      var newXs = List[Identifier]()

      val res = preMap {
        case h @ FunctionInvocation(TypedFunDef(`oracleHead`, Seq(tpe)), Seq(o)) =>
          val x = FreshIdentifier("h", tpe, true)
          newXs ::= x

          Some(x.toVariable)
        case _ => None
      }(phi)

      (newXs.reverse, res)
    }

    if (usesHoles(p.phi)) {
      val pathsToCalls = CollectorWithPaths({
          case fi: FunctionInvocation if usesHoles(fi) => fi
      }).traverse(p.phi).map(_._2)

      val pc = if (pathsToCalls.nonEmpty) {
        not(orJoin(pathsToCalls))
      } else {
        BooleanLiteral(false)
      }

      // Creates two alternative branches:
      // 1) a version with holes unreachable, on which this rule won't re-apply
      val sfact  = new TimeoutSolverFactory(sctx.solverFactory, 500L)
      val solver = SimpleSolverAPI(new TimeoutSolverFactory(sctx.solverFactory, 2000L))

      val(holesAvoidable, _) = solver.solveSAT(and(p.pc, pc))

      val avoid = if (holesAvoidable != Some(false)) {
        val newPhi = simplifyPaths(sfact)(and(pc, p.phi))
        val newProblem1 = p.copy(phi = newPhi)

        Some(decomp(List(newProblem1), {
          case List(s) if s.pre != BooleanLiteral(false) => Some(s)
          case _ => None
        }, "Avoid Holes"))
      } else {
        None
      }

      // 2) a version with holes reachable to continue applying itself
      val newPhi                 = inlineUntilHoles(p.phi)
      val (newXs, newPhiInlined) = inlineHoles(newPhi)

      val newProblem2 = p.copy(phi = newPhiInlined, xs = p.xs ::: newXs)
      val rec = Some(decomp(List(newProblem2), project(p.xs.size), "Inline Holes"))

      List(rec, avoid).flatten
    } else {
      Nil
    }
  }

  def project(firstN: Int): List[Solution] => Option[Solution] = {
    project(0 until firstN)
  }

  def project(ids: Seq[Int]): List[Solution] => Option[Solution] = {
    case List(s) =>
      Some(s.project(ids))
    case _ =>
      None
  }
}
