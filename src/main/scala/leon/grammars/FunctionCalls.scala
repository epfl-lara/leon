/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.TypeOps._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Expressions._

/** Generates non-recursive function calls
  *
  * @param currentFunction The currend function for which no calls will be generated
  * @param exclude An additional set of functions for which no calls will be generated
  */
case class FunctionCalls(prog: Program, currentFunction: FunDef, exclude: Set[FunDef]) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    val cfd = currentFunction

    def isRecursiveCall(fd: FunDef) = (prog.callGraph.transitiveCallers(cfd) + cfd) contains fd

    def isDet(fd: FunDef) = fd.body.exists(isDeterministic)

    val filter = { (fd: FunDef) => 
      !fd.isSynthetic && 
      !fd.isInner && 
      !(exclude contains fd) &&
      !isRecursiveCall(fd) &&
      isDet(fd)
    }

    for (fd <- visibleFunDefsFromMain(prog).toSeq.filter(filter).sortBy(_.id) diff prog.library.setToList.toSeq) yield {
      val tpds = fd.tparams

      val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>
        val tfd = fd.typed(tpds.map(tpd => tmap(tpd.tp)))

        val subs = fd.params.map(_.getType).map(instantiateType(_, tmap))

        val tag = Tags.tagOf(tfd.fd, isSafe = false)

        ProductionRule[TypeTree, Expr](subs, FunctionInvocation(tfd, _), tag, 1, -1.0)
      }

      SGenericProd(tpds, fd.returnType, fd.params.map(_.getType), prodBuilder)
    }
  }
}
