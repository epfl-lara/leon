/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import invariant.util.ExpressionTransformer._
import invariant.structure.FunctionUtils._
import invariant.util.LetTupleSimplification._

/**
 * A simplifier phase that eliminates tuples that are not needed
 * from function bodies, and also performs other simplifications.
 * Note: performing simplifications during instrumentation
 * will affect the validity of the information stored in function info.
 */
object ProgramSimplifier {
  val debugSimplify = false

  def apply(program: Program, instFuncs: Seq[FunDef]): Program = {
    val funMap = ((userLevelFunctions(program) ++ instFuncs).distinct).foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) => {
        val freshId = FreshIdentifier(fd.id.name, fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        accMap + (fd -> newfd)
      }
    }
    def mapExpr(ine: Expr, fd: FunDef): Expr = {
      val replaced = simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
          FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
        case _ => e
      })(ine)

      // Note: simplify only instrumented functions
      // One might want to add the maximum function to the program in the stack
      // and depth instrumentation phases if inlineMax is removed from here
      if (InstUtil.isInstrumented(fd)) {
        val allSimplifications =
          simplifyTuples _ andThen
            simplifyMax _ andThen
            simplifyLetsAndLetsWithTuples _ andThen
            simplifyAdditionsAndMax _ andThen
            inlineMax _
        allSimplifications(replaced)
      } else replaced
    }

    for ((from, to) <- funMap) {
      to.fullBody = mapExpr(from.fullBody, from)
      //copy annotations
      from.flags.foreach(to.addFlag(_))
    }
    val newprog = copyProgram(program, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if funMap.contains(fd) => funMap(fd)
      case d                                 => d
    })

    if (debugSimplify)
      println("After Simplifications: \n" + ScalaPrinter.apply(newprog))
    newprog
  }
}