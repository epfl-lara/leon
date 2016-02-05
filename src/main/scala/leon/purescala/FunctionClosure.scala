/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps._
import Constructors._
import TypeOps.instantiateType
import leon.purescala.Common.Identifier
import leon.purescala.Types.TypeParameter
import utils.GraphOps._

object FunctionClosure extends TransformationPhase {

  override val name: String = "Function Closure"
  override val description: String = "Closing function with its scoping variables"

  /** Takes a FunDef and returns a Seq of all internal FunDef's contained in fd in closed form
    * (and fd itself, without inned FunDef's).
    *
    * The strategy is as follows: Remove one layer of nested FunDef's, then call
    * close recursively on the new functions.
    */
  private def close(fd: FunDef): Seq[FunDef] = { 

    // Directly nested functions with their p.c.
    val nestedWithPathsFull = {
      val funDefs = directlyNestedFunDefs(fd.fullBody)
      collectWithPC {
        case LetDef(fd1, body) => fd1.filter(funDefs)
      }(fd.fullBody)
    }
    val nestedWithPaths = (for((fds, path) <- nestedWithPathsFull; fd <- fds) yield (fd, path)).toMap
    val nestedFuns = nestedWithPaths.keys.toSeq

    // Transitively called funcions from each function
    val callGraph: Map[FunDef, Set[FunDef]] = transitiveClosure(
      nestedFuns.map { f =>
        val calls = functionCallsOf(f.fullBody) collect {
          case FunctionInvocation(TypedFunDef(fd, _), _) if nestedFuns.contains(fd) =>
            fd
        }
        f -> calls
      }.toMap
    )

    def freeVars(fd: FunDef, pc: Expr): Set[Identifier] =
      variablesOf(fd.fullBody) ++ variablesOf(pc) -- fd.paramIds

    // All free variables one should include.
    // Contains free vars of the function itself plus of all transitively called functions.
    val transFree = nestedFuns.map { fd =>
      fd -> (callGraph(fd) + fd).flatMap( (fd2:FunDef) => freeVars(fd2, nestedWithPaths(fd2)) ).toSeq
    }.toMap

    // Closed functions along with a map (old var -> new var).
    val closed = nestedWithPaths.map {
      case (inner, pc) => inner -> step(inner, fd, pc, transFree(inner))
    }

    // Remove LetDefs from fd
    fd.fullBody = preMap({
      case LetDef(fds, bd) =>
        Some(bd)
      case _ =>
        None
    }, applyRec = true)(fd.fullBody)

    // A dummy substitution for fd, saying we should not change parameters
    val dummySubst = FunSubst(
      fd,
      Map.empty.withDefault(id => id),
      Map.empty.withDefault(id => id)
    )

    // Refresh function calls
    (dummySubst +: closed.values.toSeq).foreach {
      case FunSubst(f, callerMap, callerTMap) =>
        f.fullBody = preMap {
          case fi@FunctionInvocation(tfd, args) if closed contains tfd.fd =>
            val FunSubst(newCallee, calleeMap, calleeTMap) = closed(tfd.fd)

            // This needs some explanation.
            // Say we have caller and callee. First we find the param. substitutions of callee
            // (say old -> calleeNew) and reverse them. So we have a mapping (calleeNew -> old).
            // We also have the caller mapping, (old -> callerNew).
            // So we pass the callee parameters through these two mappings to get the caller parameters.
            val mapReverse = calleeMap map { _.swap }
            val extraArgs = newCallee.paramIds.drop(args.size).map { id =>
              callerMap(mapReverse(id)).toVariable
            }

            // Similarly for type params
            val tReverse = calleeTMap map { _.swap }
            val tOrigExtraOrdered = newCallee.tparams.map{_.tp}.drop(tfd.tps.length).map(tReverse)
            val tFinalExtra: Seq[TypeParameter] = tOrigExtraOrdered.map( tp =>
              callerTMap(tp)
            )

            Some(FunctionInvocation(
              newCallee.typed(tfd.tps ++ tFinalExtra),
              args ++ extraArgs
            ).copiedFrom(fi))
          case _ => None
        }(f.fullBody)
    }

    val funs = closed.values.toSeq.map{ _.newFd }

    // Recursively close new functions
    fd +: funs.flatMap(close)
  }

  // Represents a substitution to a new function, along with parameter and type parameter
  // mappings
  private case class FunSubst(
    newFd: FunDef,
    paramsMap: Map[Identifier, Identifier],
    tparamsMap: Map[TypeParameter, TypeParameter]
  )

  // Takes one inner function and closes it. 
  private def step(inner: FunDef, outer: FunDef, pc: Expr, free: Seq[Identifier]): FunSubst = {

    val tpFresh = outer.tparams map { _.freshen }
    val tparamsMap = outer.tparams.zip(tpFresh map {_.tp}).toMap
    
    val freshVals = (inner.paramIds ++ free).map{_.freshen}.map(instantiateType(_, tparamsMap))
    val freeMap   = (inner.paramIds ++ free).zip(freshVals).toMap

    val newFd = inner.duplicate(
      inner.id.freshen,
      inner.tparams ++ tpFresh,
      freshVals.map(ValDef(_)),
      instantiateType(inner.returnType, tparamsMap)
    )
    newFd.precondition = Some(and(pc, inner.precOrTrue))

    val instBody = instantiateType(
      newFd.fullBody,
      tparamsMap,
      freeMap
    )

    newFd.fullBody = preMap {
      case fi@FunctionInvocation(tfd, args) if tfd.fd == inner =>
        Some(FunctionInvocation(
          newFd.typed(tfd.tps ++ tpFresh.map{ _.tp }),
          args ++ freshVals.drop(args.length).map(Variable)
        ).setPos(fi))
      case _ => None
    }(instBody)

    FunSubst(newFd, freeMap, tparamsMap.map{ case (from, to) => from.tp -> to})
  }

  override def apply(ctx: LeonContext, program: Program): Program = {
    val newUnits = program.units.map { u => u.copy(defs = u.defs map {
      case m: ModuleDef =>
        m.copy(defs = m.definedClasses ++ m.definedFunctions.flatMap(close))
      case cd =>
        cd
    })}
    Program(newUnits)
  }

}
