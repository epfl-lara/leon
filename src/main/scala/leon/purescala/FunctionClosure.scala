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

  private def close(fd: FunDef): Seq[FunDef] = { 

    // Directly neste functions with their p.c.
    val nestedWithPaths = {
      val funDefs = directlyNestedFunDefs(fd.fullBody)
      collectWithPC {
        case LetDef(fd1, body) if funDefs(fd1) => fd1
      }(fd.fullBody)
    }.toMap
    
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

    // Remove LetDefs
    fd.fullBody = preMap({
      case LetDef(fd, bd) =>
        Some(bd)
      case _ =>
        None
    }, applyRec = true)(fd.fullBody)

    val dummySubst = FunSubst(
      fd,
      Map.empty.withDefault(id => id),
      Map.empty.withDefault(id => id)
    )

    // Refresh function calls
    (dummySubst +: closed.values.toSeq).foreach { case FunSubst(f, paramsMap, tparamsMap) =>
      //println(f)
      //paramsMap foreach { case (from, to) =>
      //  println(from.uniqueName + " -> " + to.uniqueName)
      //}
      f.fullBody = preMap {
        case FunctionInvocation(tfd, args) if closed contains tfd.fd =>
          val FunSubst(newFd, newParams, newTParams) = closed(tfd.fd)

          // New -> old map for function call
          val mapReverse = newParams map { _.swap }
          val extraArgs = newFd.paramIds.drop(args.size).map { id =>
            paramsMap(mapReverse(id)).toVariable
          }

          // Similarly for type params
          val tReverse = newTParams map { _.swap }
          val tOrigExtraOrdered = newFd.tparams.map{_.tp}.drop(tfd.tps.length).map(tReverse)
          val tFinalExtra: Seq[TypeParameter] = tOrigExtraOrdered.map( tp =>
            tparamsMap(tp)
          )

          Some(FunctionInvocation(
            newFd.typed(tfd.tps ++ tFinalExtra),
            args ++ extraArgs
          ))
        case _ => None
      }(f.fullBody)
    }

    val funs = closed.values.toSeq.map{ _.newFd }

    fd +: funs.flatMap(close)
  }

  private case class FunSubst(
    newFd: FunDef,
    paramsMap: Map[Identifier, Identifier],
    tparamsMap: Map[TypeParameter, TypeParameter]
  )

  private def step(inner: FunDef, outer: FunDef, pc: Expr, free: Seq[Identifier]): FunSubst = {

    val tpFresh = outer.tparams map { _.freshen }
    val tparamsMap = outer.tparams.zip(tpFresh map {_.tp}).toMap
    
    val freshVals = (inner.paramIds ++ free).map{_.freshen}.map(instantiateType(_, tparamsMap))
    val freeMap   = (inner.paramIds ++ free).zip(freshVals).toMap

    val newFd = new FunDef(
      inner.id.freshen,
      inner.tparams ++ tpFresh,
      instantiateType(inner.returnType, tparamsMap),
      freshVals.map(ValDef(_))
    )
    newFd.copyContentFrom(inner)
    newFd.precondition = Some(and(pc, inner.precOrTrue))

    val instBody = instantiateType(
      newFd.fullBody,
      tparamsMap,
      freeMap
    )

    newFd.fullBody = preMap {
      case FunctionInvocation(tfd, args) if tfd.fd == inner =>
        Some(FunctionInvocation(
          newFd.typed(tfd.tps ++ tpFresh.map{ _.tp }),
          args ++ freshVals.drop(args.length).map(Variable)
        ))
      case _ => None
    }(instBody)

    FunSubst(newFd, freeMap, tparamsMap.map{ case (from, to) => from.tp -> to})
  }

  override def apply(ctx: LeonContext, program: Program): Program = {
    val newUnits = program.units.map { u => u.copy(defs = u.defs map {
      case m: ModuleDef =>
        ModuleDef(
          m.id,
          m.definedClasses ++ m.definedFunctions.flatMap(close),
          m.isPackageObject
        )
      case cd =>
        cd
    })}
    Program(newUnits)
  }

}
