/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Definitions._
import purescala.TypeTrees._
import purescala.Extractors._
import purescala.TypeTreeOps._
import purescala.Trees._
import purescala.TreeOps._
import purescala.DefOps._
import purescala.Common._

object Helpers {
  /**
   * Filter functions potentially returning target type
   *
   * If the function takes type parameters, it will try to find an assignment
   * such that the function returns the target type.
   *
   * The return is thus a set of typed functions.
   */
  def functionsReturning(fds: Set[FunDef], tpe: TypeTree): Set[TypedFunDef] = {
    fds.flatMap { fd =>
      val free = fd.tparams.map(_.tp)
      canBeSubtypeOf(fd.returnType, free, tpe) match {
        case Some(tpsMap) =>
          Some(fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp))))
        case None =>
          None
      }
    }
  }

  def terminatingCalls(prog: Program, tpe: TypeTree, ws: Expr, pc: Expr): List[(Expr, Set[Identifier])] = {
    // TODO: Also allow calls to f(y) when: terminating(f(x)) && y == x.f 
    val terminating = prog.library.terminating.get

    val TopLevelAnds(clauses) = ws

    val gs: List[FunctionInvocation] = clauses.toList.collect {
      case FunctionInvocation(TypedFunDef(`terminating`, _), Seq(fi: FunctionInvocation)) => fi
    }

    def argsSmaller(e: Expr, tpe: TypeTree): Seq[Expr] = e match {
      case CaseClass(cct, args) =>
        (cct.fieldsTypes zip args).collect {
          case (t, e) if isSubtypeOf(t, tpe) =>
            List(e) ++ argsSmaller(e, tpe) 
        }.flatten
      case _ => Nil
    }

    gs.flatMap {
      case FunctionInvocation(tfd, args) if isSubtypeOf(tfd.returnType, tpe) =>
        val ids = tfd.params.map(vd => FreshIdentifier("<hole>", true).setType(vd.tpe)).toList

        for (((a, i), tpe) <- args.zipWithIndex zip tfd.params.map(_.tpe);
              smaller <- argsSmaller(a, tpe)) yield {
          val args = ids.map(_.toVariable).updated(i, smaller)
          (FunctionInvocation(tfd, args), ids.toSet - ids(i))
        }
      case _ =>
        Nil
    }
  }


  /**
   * All functions we call use in synthesis, which includes:
   *  - all functions in main units
   *  - all functions imported, or methods of classes imported
   */
  def functionsAvailable(p: Program): Set[FunDef] = {
    visibleFunDefsFromMain(p)
  }


}
