/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import purescala.Common._
import purescala.ExprOps.preTraversal
import purescala.Types._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Constructors._

object TypingPhase extends SimpleLeonPhase[Program, Program] {

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
   * 
   * 3) Make sure that abstract classes have at least one descendant
   */
  def apply(ctx: LeonContext, pgm: Program): Program = {
    pgm.definedFunctions.foreach(fd => {

      // Part (1)
      val argTypesPreconditions = fd.params.flatMap(arg => arg.getType match {
        case cct: ClassType if cct.parent.isDefined =>
          Seq(IsInstanceOf(arg.id.toVariable, cct))
        case at: ArrayType =>
          Seq(GreaterEquals(ArrayLength(arg.id.toVariable), IntLiteral(0)))
        case _ =>
          Seq()
      })
      argTypesPreconditions match {
        case Nil => ()
        case xs => fd.precondition = {
          fd.precondition match {
            case Some(p) => Some(andJoin(xs :+ p).copiedFrom(p))
            case None => Some(andJoin(xs))
          }
        }
      }

      fd.postcondition = fd.returnType match {
        case ct: ClassType if ct.parent.isDefined => {
          val resId = FreshIdentifier("res", ct)
          fd.postcondition match {
            case Some(p) =>
              Some(Lambda(Seq(ValDef(resId)), and(
                application(p, Seq(Variable(resId))),
                IsInstanceOf(Variable(resId), ct)
              ).setPos(p)).setPos(p))

            case None =>
              val pos = fd.body.map{ _.getPos } match {
                case Some(df: DefinedPosition) => df.focusEnd
                case _ => NoPosition
              }
              Some(Lambda(Seq(ValDef(resId)), IsInstanceOf(Variable(resId), ct)).setPos(pos))
          }
        }
        case _ => fd.postcondition
      }

      // Part (2)
      fd.body.foreach {
        preTraversal{
          case t if !t.isTyped =>
            ctx.reporter.warning(t.getPos, "Tree "+t.asString(ctx)+" is not properly typed ("+t.getPos.fullString+")")
          case _ =>
        }
      }


    })

    // Part (3)
    pgm.definedClasses.foreach {
      case acd: AbstractClassDef =>
        if (acd.knownCCDescendants.isEmpty) {
          ctx.reporter.error(acd.getPos, "Class "+acd.id.asString(ctx)+" has no concrete descendant!")
        }
      case _ =>
    }


    pgm
  }

}

