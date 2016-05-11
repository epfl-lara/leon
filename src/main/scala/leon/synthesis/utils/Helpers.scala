/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package utils

import purescala.Path
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
      subtypingInstantiation(tpe, fd.returnType) match {
        case Some(tpsMap) =>
          Some(fd.typed(fd.typeArgs.map(tp => tpsMap.getOrElse(tp, tp))))
        case None =>
          None
      }
    }
  }

  /** Given an initial set of function calls provided by a list of [[Terminating]],
    * returns function calls that will hopefully be safe to call recursively from within this initial function calls.
    *
    * For each returned call, one argument is substituted by a "smaller" one, while the rest are left as holes.
    *
    * @param prog The current program
    * @param ws Helper predicates that contain [[Terminating]]s with the initial calls
    * @param pc The path condition
    * @param tpe The expected type for the returned function calls. If absent, all types are permitted.
    * @return A list of pairs (safe function call, holes),
    *         where holes stand for the rest of the arguments of the function.
   */
  def terminatingCalls(prog: Program, ws: Expr, pc: Path, tpe: Option[TypeTree], introduceHoles: Boolean): List[(FunctionInvocation, Option[Set[Identifier]])] = {

    val TopLevelAnds(wss) = ws

    val gs: List[Terminating] = wss.toList.collect {
      case t : Terminating => t
    }

    def subExprsOf(expr: Expr, v: Variable): Option[(Variable, Expr)] = expr match {
      case CaseClassSelector(cct, r, _) => subExprsOf(r, v)
      case (r: Variable) if leastUpperBound(r.getType, v.getType).isDefined => Some(r -> v)
      case _ => None
    }

    val z   = InfiniteIntegerLiteral(0)
    val one = InfiniteIntegerLiteral(1)
    val knownSmallers = (pc.bindings.flatMap {
      // @nv: used to check both Equals(id, selector) and Equals(selector, id)
      case (id, s @ CaseClassSelector(cct, r, _)) => subExprsOf(s, id.toVariable)
      case _ => None
    } ++ pc.conditions.flatMap {
      case GreaterThan(v: Variable, `z`) =>
        Some(v -> Minus(v, one))
      case LessThan(`z`, v: Variable) =>
        Some(v -> Minus(v, one))
      case LessThan(v: Variable, `z`) =>
        Some(v -> Plus(v, one))
      case GreaterThan(`z`, v: Variable) =>
        Some(v -> Plus(v, one))
      case _ => None
    }).groupBy(_._1).mapValues(v => v.map(_._2))

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
      case Terminating(FunctionInvocation(tfd, args)) if tpe forall (isSubtypeOf(tfd.returnType, _)) =>
        val ids = tfd.params.map(vd => FreshIdentifier("<hole>", vd.getType, true)).toList

        for (((a, i), tpe) <- args.zipWithIndex zip tfd.params.map(_.getType);
              smaller <- argsSmaller(a, tpe)) yield {
          val newArgs = (if (introduceHoles) ids.map(_.toVariable) else args).updated(i, smaller)
          (FunctionInvocation(tfd, newArgs), if(introduceHoles) Some(ids.toSet - ids(i)) else None)
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
