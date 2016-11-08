/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package ir

import IRs.{ NIR, LIR }

// Lift object type to their top level type in order to properly use tagged union.
// TODO do the same for class fields!!!
// TODO use use env, maybe???
final class ClassLifter(val ctx: LeonContext) extends Transformer(NIR, LIR) with MiniReporter {
  import from._

  type Mapping = Map[ValDef, Option[to.AsA]]

  class Env(val mapping: Mapping, val liftFlag: Boolean) {
    def ++(other: Mapping) = new Env(mapping ++ other, liftFlag)
    def ++(other: Env) = new Env(mapping ++ other.mapping, liftFlag || other.liftFlag)

    def dontLift = new Env(mapping, false)
  }

  val Ø: Env = new Env(Map.empty, true) // lift type by default

  // Lift context, params & return type
  override def recImpl(fd: FunDef)(implicit env: Env): to.FunDef = {
    val id = fd.id

    val returnType = rec(fd.returnType)

    val (ctx, ctxAccess) = (fd.ctx map lift).unzip
    val (params, paramsAccess) = (fd.params map lift).unzip

    // Build our new environment
    val newEnv = env ++ ((fd.ctx ++ fd.params) zip (ctxAccess ++ paramsAccess)).toMap

    // Handle recursive functions
    val newer = to.FunDef(id, returnType, ctx, params, null)
    registerFunction(fd, newer)

    newer.body = rec(fd.body)(newEnv)

    newer
  }

  override def rec(typ: Type)(implicit env: Env): to.Type = super.rec(typ) match {
    case to.ClassType(clazz) if env.liftFlag => to.ClassType(clazz.hierarchyTop)
    case typ => typ
  }

  // Lift only for classes, return (vd, None) for, e.g., primitive or array
  private def lift(vd0: ValDef)(implicit env: Env): (to.ValDef, Option[to.AsA]) = {
    val vd = rec(vd0)

    val typ = rec(vd0.getType)(env.dontLift)
    val access = typ match {
      case ct @ to.ClassType(_) => Some(to.AsA(to.Binding(vd), ct))
      case _ => None
    }

    vd -> access
  }

}

