/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.DefOps._
import purescala.Expressions._
import purescala.TypeOps.canBeSubtypeOf
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Extractors._
import leon.solvers.{SolverFactory, SimpleSolverAPI}
import leon.utils.Simplifiers

object Abduction extends Rule("Abduction") {
  override def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {

    // Let ⟦ as ⟨ ws && pc | phi ⟩ xs ⟧ be the original problem
    def processFd(tfd: TypedFunDef): Option[RuleInstantiation] = {
      // We assign xs = tfd(newXs), newXs fresh
      val newXs = tfd.paramIds map (_.freshen)
      val args  = newXs map Variable
      val call  = FunctionInvocation(tfd, args)
      // prec. of tfd(newXs) (newXs have to satisfy it)
      val pre   = replaceFromIDs(tfd.paramIds.zip(args).toMap, tfd.precOrTrue)

      // Fail if pre is not SAT
      val solver = SimpleSolverAPI(SolverFactory.getFromSettings(hctx, hctx.program))
      if (!solver.solveSAT(p.pc and pre)._1.contains(true)) return None

      // postc. of tfd(newXs) will hold for xs
      val post  = application(
        replaceFromIDs(tfd.paramIds.zip(args).toMap, tfd.postOrTrue),
        Seq(tupleWrap(p.xs map Variable))
      )

      // Conceptually, the new problem is
      // ⟦ as ⟨ ws && pc && xs <- tfd(newXs) && post | pre && phi ⟩ newXs ⟧
      // But we will only accept this problem if xs is simplifiable in phi under the new assumptions

      def containsXs(e: Expr) = (variablesOf(e) & p.xs.toSet).nonEmpty

      val newPhi = {

        val newPhi0 = {
          // Try to eliminate xs in trivial cases
          val TopLevelAnds(newPhis) = and(pre, post)
          val equalities = newPhis.collect {
            case Equals(e1, e2) if containsXs(e1) && !containsXs(e2) => e1 -> e2
            case Equals(e1, e2) if containsXs(e2) && !containsXs(e1) => e2 -> e1
          }.toMap

          replace(equalities, p.phi)
        }

        val bigX = FreshIdentifier("x", p.outType, alwaysShowUniqueID = true)

        val projections = unwrapTuple(call, p.xs.size).zipWithIndex.map{
          case (e, ind) => tupleSelect(e, ind + 1, p.xs.size)
        }

        val pc = p.pc
          .withCond(pre)
          .withBinding(bigX, call)
          .withBindings(newXs zip projections)
          .withCond(post)

        Simplifiers.bestEffort(hctx, hctx.program)(newPhi0, pc)
      }

      if (containsXs(newPhi)) {
        None
      } else {
        // We do not need xs anymore, so we accept the decomposition.
        // We can remove xs-related cluases from the PC.
        // Notice however we need to synthesize newXs such that pre is satisfied as well.
        // Final problem is:
        // ⟦ as ⟨ ws && pc | pre && phi ⟩ newXs ⟧

        val newP = p.copy(phi = newPhi, xs = newXs.toList)

        val onSuccess = forwardMap(letTuple(p.xs, call, _))

        Some(decomp(List(newP), onSuccess, "Blah"))
      }
    }

    val filter = (fd: FunDef) => fd.isSynthetic || fd.isInner

    val funcs = visibleFunDefsFromMain(hctx.program).toSeq.sortBy(_.id).filterNot(filter)

    // For now, let's handle all outputs at once only
    for {
      fd <- funcs
      inst <- canBeSubtypeOf(p.outType, fd.tparams.map(_.tp), fd.returnType)
      decomp <- processFd(fd.typed(fd.tparams map (tpar => inst(tpar.tp))))
    } yield decomp

  }

}
