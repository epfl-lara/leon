/* Copyright 2009-2016 EPFL, Lausanne */

package leon.utils

import leon._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.TypeOps.instantiateType
import purescala.ExprOps._
import purescala.Extractors._
import purescala.DefOps._
import purescala.Constructors.{ caseClassSelector, application }
import invariant.util.LetTupleSimplification._

/**
 * Recursive functions are inlined once. A function with contracts is inlined only if
 * its invocations are top level expression of the body. Otherwise, we throw an error.
 */
object HOInliningPhase extends TransformationPhase {

  val name = "Inline @inline functions in --mem extension"
  val description = "Inline functions marked as @inline and remove their definitions. For use in --mem option"

  def apply(ctx: LeonContext, p: Program): Program = {
    // Detect inlined functions that are recursive
    val inlineOnce = p.definedFunctions.filter(fd => fd.flags(IsInlined)).flatMap {
      case fd if p.callGraph.isRecursive(fd) =>
        ctx.reporter.warning("Inlining recursive functions only once '" + fd.id.asString(ctx) + "'!")
        Seq(fd)
      case fd if !fd.hasBody =>
        ctx.reporter.warning("Refusing to inline bodyless functions '" + fd.id.asString(ctx) + "'!")
        Seq()
      case _ => Seq()
    }.toSet

    def doInline(fd: FunDef) = fd.flags(IsInlined)

    def trivialPost(fd: FunDef) = fd.postcondition match {
      case None                                  => true
      case Some(Lambda(_, BooleanLiteral(true))) => true
      case _                                     => false
    }

    var incompleteFunctions = Set[FunDef]()
    def rec(topLevel: Boolean, inlinedFuns: Set[FunDef])(e: Expr): Expr = e match {
      case FunctionInvocation(tfd, args) if doInline(tfd.fd) =>
        if (!topLevel && (!trivialPost(tfd.fd) || tfd.fd.precOrTrue != BooleanLiteral(true))) {
          ctx.reporter.warning("Refusing to inline function with non-trivial contracts inside expressions '" + tfd.id.asString(ctx) + "'!")
          incompleteFunctions += tfd.fd
          e
        } else {
          val body = if (topLevel) tfd.fullBody else tfd.body.get
          val argsMap = (tfd.params.map(_.id) zip args).toMap
          if (inlineOnce(tfd.fd)) {
            if (!inlinedFuns(tfd.fd))
              rec(topLevel, inlinedFuns + tfd.fd)(replaceFromIDs(argsMap, body))
            else {
              // here, we have inlined a recursive function once, so do nothing
              e
            }
          } else {
            // create lets to bind the args to variables
            val (flatArgs, letCons) = args.foldRight((Seq[Variable](), (e: Expr) => e)) {
              case (arg: Variable, (fargs, lcons)) =>
                (arg +: fargs, lcons)
              case (arg, (fargs, lcons)) =>
                val id = FreshIdentifier("a", arg.getType, true)
                (id.toVariable +: fargs, e => Let(id, arg, lcons(e)))
            }
            val formalToActual = (tfd.params.map(_.id) zip flatArgs).toMap
            val substExpr = letCons(replaceFromIDs(formalToActual, body))
            val nexpr = simplerLet(substExpr)
            rec(topLevel, inlinedFuns)(nexpr)
          }
        }

      case CaseClassSelector(cct, cc: CaseClass, id) =>
        caseClassSelector(cct, cc, id)
      case Application(caller: Lambda, args) =>
        rec(false, inlinedFuns)(application(caller, args))
      case Operator(args, op) =>
        op(args map rec(false, inlinedFuns))
    }

    for (fd <- p.definedFunctions) {
      fd.fullBody = rec(true, Set())(fd.fullBody)
    }
    filterFunDefs(p, fd => !doInline(fd) || incompleteFunctions(fd) || inlineOnce(fd))
  }

}
