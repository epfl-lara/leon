/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._

/*
 * The main idea is to add ReferenceType on functions' parameters when either:
 *  - the parameter is not an array (C array are always passed by reference using a different mechanism)
 *  - the parameter is part of the context of the function
 *  - the parameter is of mutable type
 *
 * This also means that when using a binding in an expression we have to make sure that we
 * take a reference or dereference it before using it.
 *
 * Array are mutables, but once converted into C they are wrapped into an immutable struct;
 * we therefore do not take array by reference because this would only add an indirection
 */
final class Referentiator(val ctx: LeonContext) extends Transformer(CIR, RIR) with MiniReporter {
  import from._

  type Env = Map[CIR.ValDef, RIR.ValDef]
  val Ø = Map[CIR.ValDef, RIR.ValDef]()

  override def recImpl(fd: FunDef)(implicit env: Env): to.FunDef = {
    val id = fd.id

    val returnType = rec(fd.returnType) // nothing special thanks to the no-aliasing rule

    val ctx = fd.ctx map { c0 =>
      // except for arrays, add ReferenceType
      val c = rec(c0)
      if (c.isArray) c
      else toReference(c)
    }

    val params = fd.params map { p0 =>
      // except for arrays, add ReferenceType to mutable types
      val p = rec(p0)
      if (p.isArray) p
      else if (p.isMutable) toReference(p)
      else p
    }

    // Build the new environment: from CIR to RIR
    val newEnv = env ++ ((fd.ctx ++ fd.params) zip (ctx ++ params))

    // Handle recursive functions
    val newer = to.FunDef(id, returnType, ctx, params, null)
    registerFunction(fd, newer)

    newer.body = rec(fd.body)(newEnv)

    newer
  }

  // When converting a binding we add Deref if the variable is known to be
  // a reference. When converting, say, a function call we add Ref if the
  // expected parameter is of ReferenceType, or Deref in the opposite
  // situation.
  //
  // These operations can introduce pattern such as Deref(Ref(_))
  // or Ref(Deref(_)). This is of course not what we want so we fix it
  // right away using the ref & deref factory functions.
  final override def recImpl(e: Expr)(implicit env: Env): (to.Expr, Env) = e match {
    case Binding(vd0) =>
      // Check the environment for id; if it's a ref we have to reference it.
      val vd = env(vd0)
      val b = RIR.Binding(vd)
      if (vd.isReference) deref(b) -> env
      else b -> env

    case Decl(_) => internalError("Decl is expected only after normalisation/flattening")

    case DeclInit(vd0, value0) =>
      val vd = rec(vd0)
      val value = rec(value0)
      val newEnv = env + (vd0 -> vd)
      to.DeclInit(vd, value) -> newEnv

    case Ref(_) | Deref(_) => internalError("Ref & Deref expression should not yet be present")

    case App(fd0, extra0, args0) =>
      // Add Ref/Deref to extra/args when appropriate
      val fd = rec(fd0)
      val extra = refMatch(fd.ctx)(extra0 map rec)
      val args = refMatch(fd.params)(args0 map rec)

      to.App(fd, extra, args) -> env

    case Construct(cd0, args0) =>
      val cd = rec(cd0)
      val args = refMatch(cd.fields)(args0 map rec)

      to.Construct(cd, args) -> env

    case e => super.recImpl(e)
  }

  // Adapt the expressions to match w.r.t. references the given parameter types, for argument-like expressions.
  private def refMatch(params: Seq[RIR.ValDef])(args: Seq[RIR.Expr]): Seq[RIR.Expr] = {
    (params zip args) map { case (param, arg) =>
      val pr = param.isReference
      val ar = arg.getType.isReference

      (pr, ar) match {
        case (false, false) | (true, true) => arg
        case (false, true) => deref(arg)
        case (true, false) => ref(arg, shortLived = true)
      }
    }
  }

  // Build Ref & Deref expression without patterns such as Ref(Deref(_))
  private def ref(e: RIR.Expr, shortLived: Boolean = false): RIR.Expr = e match {
    case b @ RIR.Binding(_) => RIR.Ref(b)
    case RIR.Deref(e) => e

    // NOTE Reference can be build on Constructor, but we have to make sure we
    //      don't take the reference of a temporary result for a too long period.
    case ctor @ RIR.Construct(_, _) if shortLived => RIR.Ref(ctor)

    case _ => internalError(s"Making reference on an unsupported expression: $e")
  }

  private def deref(e: RIR.Expr): RIR.Expr = e match {
    case b @ RIR.Binding(vd) if vd.isReference => RIR.Deref(b)
    case RIR.Ref(e) => e
    case _ => internalError(s"Dereferencing an unsupported expression: $e")
  }

  private def toReference(vd: RIR.ValDef) = vd.copy(typ = RIR.ReferenceType(vd.typ))

}

