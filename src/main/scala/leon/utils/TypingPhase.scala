/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Common._
import purescala.TreeOps.preTraversal
import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._

object TypingPhase extends LeonPhase[Program, Program] {

  val name = "Typing"
  val description = "Ensure and enforce certain Leon typing rules"

  /**
   * This phase does 2 different things:
   *
   * 1) Ensure that functions that take and/or return a specific ADT subtype
   *    have this encoded explicitly in pre/postconditions. Solvers such as Z3
   *    unify types, which means that we need to ensure models are consistent
   *    with the original type constraints.
   *
   * 2) Report warnings in case parts of the tree are not correctly typed
   *    (Untyped).
   */
  def run(ctx: LeonContext)(pgm: Program): Program = {
    pgm.definedFunctions.foreach(fd => {

      // Part (1)
      fd.precondition = {
        val argTypesPreconditions = fd.params.flatMap(arg => arg.tpe match {
          case cct : CaseClassType => Seq(CaseClassInstanceOf(cct, arg.id.toVariable))
          case _ => Seq()
        })
        argTypesPreconditions match {
          case Nil => fd.precondition
          case xs => fd.precondition match {
            case Some(p) => Some(And(p +: xs))
            case None => Some(And(xs))
          }
        }
      }

      fd.postcondition = fd.returnType match {
        case cct : CaseClassType => {

          fd.postcondition match {
            case Some((id, p)) =>
              Some((id, And(CaseClassInstanceOf(cct, Variable(id)).setPos(p), p).setPos(p)))

            case None =>
              val resId = FreshIdentifier("res").setType(cct)

              Some((resId, CaseClassInstanceOf(cct, Variable(resId))))
          }
        }
        case _ => fd.postcondition
      }

      // Part (2)
      fd.body.foreach {
        preTraversal{
          case t if !t.isTyped =>
            ctx.reporter.warning("Tree "+t.asString(ctx)+" is not properly typed ("+t.getPos.fullString+")")
          case _ =>
        }
      }

    })
    pgm
  }

}

