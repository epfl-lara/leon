/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps._
import TypeOps.instantiateType
import Common.Identifier
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
  def close(fd: FunDef): Seq[FunDef] = {

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
          case FunctionInvocation(TypedFunDef(fd, _), _) if nestedFuns.contains(fd) => fd
        }

        val pcCalls = functionCallsOf(nestedWithPaths(f).fullClause) collect {
          case FunctionInvocation(TypedFunDef(fd, _), _) if nestedFuns.contains(fd) => fd
        }

        f -> (calls ++ pcCalls)
      }.toMap
    )
    //println("nested funs: " + nestedFuns)
    //println("call graph: " + callGraph)

    def freeVars(fd: FunDef, pc: Path): Set[Identifier] =
      variablesOf(fd.fullBody) ++ pc.variables ++ pc.bindings.map(_._1) -- fd.paramIds

    // All free variables one should include.
    // Contains free vars of the function itself plus of all transitively called functions.
    // also contains free vars from PC if the PC is relevant to the fundef
    val transFreeWithBindings = {
      def step(current: Map[FunDef, Set[Identifier]]): Map[FunDef, Set[Identifier]] = {
        nestedFuns.map(fd => {
          val transFreeVars = (callGraph(fd) + fd).flatMap((fd2:FunDef) => current(fd2))
          val reqPath = nestedWithPaths(fd).filterByIds(transFreeVars)
          (fd, transFreeVars ++ freeVars(fd, reqPath))
        }).toMap
      }

      utils.fixpoint(step, -1)(nestedFuns.map(fd => (fd, variablesOf(fd.fullBody) -- fd.paramIds)).toMap)
    }

    val transFree: Map[FunDef, Seq[Identifier]] = 
      //transFreeWithBindings.map(p => (p._1, p._2 -- nestedWithPaths(p._1).bindings.map(_._1))).map(p => (p._1, p._2.toSeq))
      transFreeWithBindings.map(p => (p._1, p._2.toSeq))


    // Closed functions along with a map (old var -> new var).
    val closed = nestedWithPaths.map {
      case (inner, pc) => inner -> closeFd(inner, fd, pc, transFree(inner))
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
          case fi @ FunctionInvocation(tfd, args) if closed contains tfd.fd =>
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
    funs foreach (_.addFlag(IsInner))

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
  private def closeFd(inner: FunDef, outer: FunDef, pc: Path, free: Seq[Identifier]): FunSubst = {
    //println("inner: " + inner)
    //println("pc: " + pc)
    //println("free: " + free.map(_.uniqueName))

    val reqPC = pc.filterByIds(free.toSet)

    val tpFresh = outer.tparams map { _.freshen }
    val tparamsMap = outer.typeArgs.zip(tpFresh map {_.tp}).toMap
    
    val freshVals = (inner.paramIds ++ free).map{_.freshen}.map(instantiateType(_, tparamsMap))
    val freeMap   = (inner.paramIds ++ free).zip(freshVals).toMap
    val freshParams = (inner.paramIds ++ free).filterNot(v => reqPC.isBound(v)).map(v => freeMap(v))

    val newFd = inner.duplicate(
      inner.id.freshen,
      inner.tparams ++ tpFresh,
      freshParams.map(ValDef(_)),
      instantiateType(inner.returnType, tparamsMap)
    )

    val instBody = instantiateType(
      withPath(newFd.fullBody, reqPC),
      tparamsMap,
      freeMap
    )

    newFd.fullBody = preMap {
      case Let(id, v, r) if freeMap.isDefinedAt(id) => Some(Let(freeMap(id), v, r))
      case fi @ FunctionInvocation(tfd, args) if tfd.fd == inner =>
        Some(FunctionInvocation(
          newFd.typed(tfd.tps ++ tpFresh.map{ _.tp }),
          args ++ freshParams.drop(args.length).map(Variable)
        ).setPos(fi))
      case _ => None
    }(instBody)

    //HACK to make sure substitution happened even in nested fundef
    newFd.fullBody = replaceFromIDs(freeMap.map(p => (p._1, p._2.toVariable)), newFd.fullBody)


    FunSubst(newFd, freeMap, tparamsMap)
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
