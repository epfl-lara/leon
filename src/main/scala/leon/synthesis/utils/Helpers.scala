/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Definitions._
import purescala.Types._
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Expressions._
import purescala.DefOps._
import purescala.Common._
import Witnesses._

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

    val TopLevelAnds(wss) = ws
    val TopLevelAnds(clauses) = pc

    val gs: List[Terminating] = wss.toList.collect {
      case t : Terminating => t
    }

    def subExprsOf(expr: Expr, v: Variable): Option[(Variable, Expr)] = expr match {
      case CaseClassSelector(cct, r, _) => subExprsOf(r, v)
      case (r: Variable) if leastUpperBound(r.getType, v.getType).isDefined => Some(r -> v)
      case _ => None
    }
    
    val knownSmallers = clauses.collect {
      case Equals(v: Variable, s@CaseClassSelector(cct, r, _)) => subExprsOf(s, v)
      case Equals(s@CaseClassSelector(cct, r, _), v: Variable) => subExprsOf(s, v)
    }.flatten.groupBy(_._1).mapValues(v => v.map(_._2))

    def argsSmaller(e: Expr, tpe: TypeTree): Seq[Expr] = e match {
      case CaseClass(cct, args) =>
        (cct.fieldsTypes zip args).collect {
          case (t, e) if isSubtypeOf(t, tpe) =>
            List(e) ++ argsSmaller(e, tpe) 
        }.flatten
      case v: Variable =>
        knownSmallers.getOrElse(v, Seq())

      case _ => Nil
    }

    val res = gs.flatMap {
      case Terminating(tfd, args) if isSubtypeOf(tfd.returnType, tpe) =>
        val ids = tfd.params.map(vd => FreshIdentifier("<hole>", vd.getType, true)).toList

        for (((a, i), tpe) <- args.zipWithIndex zip tfd.params.map(_.getType);
              smaller <- argsSmaller(a, tpe)) yield {
          val args = ids.map(_.toVariable).updated(i, smaller)
          (FunctionInvocation(tfd, args), ids.toSet - ids(i))
        }
      case _ =>
        Nil
    }

    res
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
