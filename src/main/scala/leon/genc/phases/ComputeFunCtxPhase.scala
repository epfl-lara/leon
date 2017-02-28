/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import purescala.Common.{ Identifier }
import purescala.Definitions.{ FunDef, ValDef }
import purescala.Expressions._
import purescala.Extractors.{ Operator }
import xlang.Expressions._

import scala.collection.mutable.{ Map => MutableMap }

/*
 * Compute, for each function definition, its context; i.e. roughly the set of free variable of its body.
 *
 * NOTE we are overapproximating the set of free variable by capturing any value defined "upstream"
 *      in the AST.
 *
 * NOTE in C99 there's the concept of strict aliasing (cf. §6.5/7), but since we don't do any weird
 *      cast operation in our translation, the overapproximation mentioned above is not an issue.
 */
private[genc] object ComputeFunCtxPhase extends TimedLeonPhase[Dependencies, FunCtxDB] {
  val name = "Function context computer"
  val description = "Compute the context of each given function definition"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("build function contexts database")

  def apply(ctx: LeonContext, deps: Dependencies): FunCtxDB = {
    val reporter = MiniReporter(ctx)
    import reporter._

    type Ctx = Seq[VarInfo]

    val db = MutableMap[FunDef, Seq[VarInfo]]()

    def toVarInfo(vd: ValDef) = VarInfo(vd.id, vd.getType, vd.isVar)

    def processFunction(fd: FunDef, ctx: Ctx): Unit = {
      debug(s"Registering ${fd.id.name} with ${ctx map { _.id } mkString ", "}.")
      db += fd -> ctx

      // Recurse on body with an extended context
      val ctx2 = ctx ++ (fd.params map toVarInfo)
      rec(fd.fullBody, ctx2)
    }

    def rec(expr: Expr, ctx: Ctx): Unit = expr match {
      // Handle the interesting cases first, or they will fall into `case Operator(args, _)`.
      case Let(binder, value, rest) =>
        rec(value, ctx) // binder not yet available here!
        val ctx2 = ctx :+ VarInfo(binder, binder.getType, isVar = false)
        rec(rest, ctx2)

      case LetVar(binder, value, rest) =>
        rec(value, ctx) // binder not yet available here!
        val ctx2 = ctx :+ VarInfo(binder, binder.getType, isVar = true)
        rec(rest, ctx2)

      case LetDef(fds, rest) =>
        // Register the nested functions, and recurse
        fds foreach { fd => processFunction(fd, ctx) }
        rec(rest, ctx)

      // Because technically a function could be defined in a block which is itself an argument,
      // we recurse on arguments as well!
      // This also includes Terminal-like expression and therefore stop recursion when needed.
      case Operator(args, _) => args foreach { arg => rec(arg, ctx) }

      case _ => internalError(s"NOT YET IMPLEMENTED: ctx computation for ${expr.getClass}")
    }

    // Process every top level function to register function contextes for their inner functions;
    // Register those top level functions as well
    val topLevelFuns: Set[FunDef] = deps.deps collect { case fd: FunDef => fd }
    val Ø = Seq[VarInfo]()
    topLevelFuns foreach { fd => processFunction(fd, Ø) }

    db.toMap // Make it immutable
  }

}

